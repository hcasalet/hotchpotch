import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

type Var = String

data Const = CInt Integer
           | CBool Bool
           deriving (Show, Eq, Ord)

data Expr     =  Var Var
              |  Con Const
              |  App Expr Expr
              |  Lam String Expr
              |  Let String Expr Expr
              |  If Expr Expr Expr
              deriving (Show, Eq, Ord)

data Type    =  TVar Var
             |  TCon String
             |  TFun Type Type
             deriving (Show, Eq, Ord)

data Scheme = Forall [Var] Type

newtype TypeEnv = TypeEnv (Map.Map Var Scheme)

extend :: TypeEnv -> (Var, Scheme) -> TypeEnv
extend (TypeEnv env) (x, s) = TypeEnv $ Map.insert x s env

class Types a where
    apply  ::  Subst -> a -> a
    ftv    ::  a -> Set.Set String

instance Types Type where
    apply _ (TCon a)      = TCon a
    apply s (TVar n)      =  case Map.lookup n s of
                               Nothing  -> TVar n
                               Just t   -> t
    apply s (TFun t1 t2)  = TFun (apply s t1) (apply s t2)
    ftv (TVar n)      =  Set.singleton n
    ftv TCon{}          =  Set.empty
    ftv (TFun t1 t2)  =  ftv t1 `Set.union` ftv t2

instance Types Scheme where
    ftv (Forall vars t)          = ftv t `Set.difference` (Set.fromList vars)
    apply s (Forall vars t)      = Forall vars $ apply s' t
                                 where s' = foldr Map.delete s vars

instance Types a => Types [a] where
    ftv l    =  foldr Set.union Set.empty (map ftv l)
    apply s  =  map (apply s)

instance Types TypeEnv where
    ftv (TypeEnv env)      =  ftv $ Map.elems env
    apply s (TypeEnv env)  =  TypeEnv $ Map.map (apply s) env

type Subst = Map.Map String Type
nullSubst  ::  Subst
nullSubst  =   Map.empty
composeSubst         :: Subst -> Subst -> Subst
composeSubst s1 s2   = (Map.map (apply s1) s2) `Map.union` s1

generalize        ::  TypeEnv -> Type -> Scheme
generalize env t  =   Forall vars t
    where vars = Set.toList ((ftv t) `Set.difference` (ftv env))

newTyVar :: String -> TypeInfer Type
newTyVar prefix =
        do  s <- get
            put s{inferenceSupply = inferenceSupply s + 1}
            return (TVar  (prefix ++ show (inferenceSupply s)))

instantiate :: Scheme -> TypeInfer Type
instantiate (Forall vars t) = do  nvars <- mapM (\ _ -> newTyVar "a") vars
                                  let s = Map.fromList (zip vars nvars)
                                  return $ apply s t

data TypeInferEnv = TypeInferEnv  {}

data TypeInferState = TypeInferState {  inferenceSupply :: Int,
                            inferenceSubst :: Subst}

type TypeInfer a = ExceptT String (ReaderT TypeInferEnv (StateT TypeInferState IO)) a

runTypeInfer :: TypeInfer a -> IO (Either String a, TypeInferState)
runTypeInfer t =
      do (res, st) <- runStateT (runReaderT (runExceptT t) initTIEnv) initTIState
         return (res, st)
    where initTIEnv = TypeInferEnv{}
          initTIState = TypeInferState{inferenceSupply = 0,
                                inferenceSubst = Map.empty}

unify :: Type -> Type -> TypeInfer Subst
unify (TCon a) (TCon b) | a == b      = return nullSubst
unify (TVar u) t                      =  varBind u t
unify t (TVar u)                      =  varBind u t
unify (TFun l r) (TFun l' r')         =  do  s1 <- unify l l'
                                             s2 <- unify (apply s1 r) (apply s1 r')
                                             return (s1 `composeSubst` s2)
unify t1 t2                           =  throwError $ "types do not unify: " ++ show t1 ++
                                       " vs. " ++ show t2

occursCheck ::  Types a => String -> a -> Bool
occursCheck a t = a `Set.member` ftv t

varBind :: String -> Type -> TypeInfer Subst
varBind u t  | t == TVar u           =  return nullSubst
             | occursCheck u t       =  throwError $ "occurs check fails: " ++ u ++ " : " ++ show t
             | otherwise             =  return (Map.singleton u t)

infer        ::  TypeEnv -> Expr -> TypeInfer (Subst, Type)
infer (TypeEnv env) (Con l) =
    case l of
        CInt n -> return (nullSubst, TCon "Int")
        CBool n -> return (nullSubst, TCon "Bool")
infer (TypeEnv env) (Var n) =
    case Map.lookup n env of
        Nothing     ->  throwError $ "unbound variable: " ++ n
        Just sigma  ->  do t <- instantiate sigma
                           return (nullSubst, t)
infer env (Lam n e) =
    do  tv <- newTyVar "a"
        let env' = env `extend` (n, Forall [] tv)
        (s1, t1) <- infer env' e
        return (s1, TFun (apply s1 tv) t1)
infer env (App e1 e2) =
    do  tv <- newTyVar "a"
        (s1, t1) <- infer env e1
        (s2, t2) <- infer (apply s1 env) e2
        s3 <- unify (apply s2 t1) (TFun t2 tv)
        return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
infer env (Let x e1 e2) =
    do  (s1, t1) <- infer env e1
        let    t' = generalize (apply s1 env) t1
        (s2, t2) <- infer ((apply s1 env) `extend` (x, t')) e2
        return (s1 `composeSubst` s2, t2)
infer env (If e1 e2 e3) =
    do  (s1, t1) <- infer env e1
        (s2, t2) <- infer env e2
        (s3, t3) <- infer env e3
        s4 <- unify t1 (TCon "Bool")
        s5 <- unify t2 t3
        return (s5 `composeSubst` s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1, apply s5 t2)

typeInference :: Map.Map String Scheme -> Expr -> TypeInfer Type
typeInference env e =
    do  (s, t) <- infer (TypeEnv env) e
        return (apply s t)

-- $$$$$$$$$$$$$$$$$$$
-- Test Cases
-- $$$$$$$$$$$$$$$$$$$
-- App (lambda x).15 25 => type: TCon "Int"
e1  = App (Lam "x" (Con (CInt 15))) (Con (CInt 25))

-- App (lambda x).False 25 => type: TCon "Bool"
e2  = App (Lam "x" (Con (CBool False))) (Con (CInt 25))

-- App (lambda x).15 False => type: TCon "Int"
e3 = App (Lam "x" (Con (CInt 15))) (Con (CBool False))

-- let y = (lambda x).0 y => type: TFun (TVAR "a1") (TCon "Int")
e4  =  Let "y" (Lam "x" (Con (CInt 0)))
        (Var "y")

-- let y = (lambda x).False y => type: TFun (TVar "a1") (TCon "Bool")
e5  =  Let "y" (Lam "x" (Con (CBool False)))
        (Var "y")

-- (lambda m).(let x m (let y x(true)) y)  => TFun (TFun (TCon "Bool") (TVar "a1")) (TVar "a1")
e6  =  Lam "m" (Let "x" (Var "m")
                 (Let "y" (App (Var "x") (Con (CBool True)))
                       (Var "y")))

-- If e1 then e2 else e3 => TCon "Int" (e2 (or e3))
e7  = If (Con (CBool True)) (App (Lam "x" (Con (CInt 15))) (Con (CInt 25)))
        (Let "id" (Lam "x" (Var "x")) (App (App (Var "id") (Var "id")) (Con (CInt 109))))

-- If e1 then e2 else e3 => type error as e1 is not TBool
e8  = If (Con (CInt 5)) (Let "y" (Lam "x" (Var "x")) (Var "y"))
         (Let "id" (Lam "x" (Var "x")) (App (Var "id") (Var "id")))

-- If e1 then e2 else e3 => type error as e2 and e3 do not unify
e9  = If (Con (CBool True)) (App (Lam "x" (Con (CBool False))) (Con (CInt 25)))
         (App (Lam "x" (Con (CInt 15))) (Con (CInt 25)))

-- Let id (Lamda x).(App x x) id => type error
e10  =  Let "id" (Lam "x" (App (Var "x") (Var "x")))
        (Var "id")


test :: Expr -> IO ()
test e =
    do  (res, _) <- runTypeInfer (typeInference Map.empty e)
        case res of
          Left err  ->  putStrLn $ show e ++ "\n" ++ "Error: " ++ err ++ "\n"
          Right t   ->  putStrLn $ show e ++ "\n" ++ "Type:  " ++ show t ++ "\n"

main :: IO ()
main = mapM_ test [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
