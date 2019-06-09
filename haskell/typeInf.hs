import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

type Var = String
type Subst = Map.Map String Type

data Const = CInt Integer
           | CBool Bool
           deriving (Show, Eq, Ord)

data Type    =  TVar Var
             |  TCon String
             |  TFun Type Type
             |  TList [Var]
             deriving (Show, Eq, Ord)

data Scheme = Forall [Var] Type

newtype TypeEnv = TypeEnv (Map.Map Var Scheme)

extend :: TypeEnv -> (Var, Scheme) -> TypeEnv
extend (TypeEnv env) (x, s) = TypeEnv $ Map.insert x s env

data Expr     =  Var Var
              |  Con Const
              |  App Expr Expr
              |  Lam String Expr
              |  Let String Expr Expr
              |  If Expr Expr Expr
              deriving (Show, Eq, Ord)

class Types a where
    applysubstitution  ::  Subst -> a -> a
    freetypevariable    ::  a -> Set.Set String

instance Types Type where
    applysubstitution _ (TCon a)      = TCon a
    applysubstitution s (TVar n)      =  case Map.lookup n s of
                               Nothing  -> TVar n
                               Just t   -> t
    applysubstitution s (TFun t1 t2)  = TFun (applysubstitution s t1) (applysubstitution s t2)
    freetypevariable (TVar n)      =  Set.singleton n
    freetypevariable TCon{}        =  Set.empty
    freetypevariable (TFun t1 t2)  =  freetypevariable t1 `Set.union` freetypevariable t2

instance Types Scheme where
    freetypevariable (Forall vars t)         = freetypevariable t `Set.difference` (Set.fromList vars)
    applysubstitution s (Forall vars t)      = Forall vars $ applysubstitution s' t
                                 where s' = foldr Map.delete s vars

instance Types a => Types [a] where
    freetypevariable l   =  foldr Set.union Set.empty (map freetypevariable l)
    applysubstitution s  =  map (applysubstitution s)

instance Types TypeEnv where
    freetypevariable (TypeEnv env)     =  freetypevariable $ Map.elems env
    applysubstitution s (TypeEnv env)  =  TypeEnv $ Map.map (applysubstitution s) env

-- Substitution
nullSubst  ::  Subst
nullSubst  =   Map.empty

composeSubst         :: Subst -> Subst -> Subst
composeSubst s1 s2   = (Map.map (applysubstitution s1) s2) `Map.union` s1

-- Generalization
generalize        ::  TypeEnv -> Type -> Scheme
generalize env t  =   Forall vars t
    where vars = Set.toList ((freetypevariable t) `Set.difference` (freetypevariable env))

newTypeVar :: String -> TypeInfer Type
newTypeVar prefix =
        do  s <- get
            put s{inferenceSupply = inferenceSupply s + 1}
            return (TVar  (prefix ++ show (inferenceSupply s)))

instantiate :: Scheme -> TypeInfer Type
instantiate (Forall vars t) = do  nvars <- mapM (\ _ -> newTypeVar "a") vars
                                  let s = Map.fromList (zip vars nvars)
                                  return $ applysubstitution s t

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
                                             s2 <- unify (applysubstitution s1 r) (applysubstitution s1 r')
                                             return (s1 `composeSubst` s2)
unify t1 t2                           =  throwError $ "types do not unify: " ++ show t1 ++
                                       " vs. " ++ show t2

occursCheck ::  Types a => String -> a -> Bool
occursCheck a t = a `Set.member` freetypevariable t

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
    do  tv <- newTypeVar "a"
        let env' = env `extend` (n, Forall [] tv)
        (s1, t1) <- infer env' e
        return (s1, TFun (applysubstitution s1 tv) t1)
infer env (App e1 e2) =
    do  tv <- newTypeVar "a"
        (s1, t1) <- infer env e1
        (s2, t2) <- infer (applysubstitution s1 env) e2
        s3 <- unify (applysubstitution s2 t1) (TFun t2 tv)
        return (s3 `composeSubst` s2 `composeSubst` s1, applysubstitution s3 tv)
infer env (Let x e1 e2) =
    do  (s1, t1) <- infer env e1
        let    t' = generalize (applysubstitution s1 env) t1
        (s2, t2) <- infer ((applysubstitution s1 env) `extend` (x, t')) e2
        return (s1 `composeSubst` s2, t2)
infer env (If e1 e2 e3) =
    do  (s1, t1) <- infer env e1
        (s2, t2) <- infer env e2
        (s3, t3) <- infer env e3
        s4 <- unify t1 (TCon "Bool")
        s5 <- unify t2 t3
        return (s5 `composeSubst` s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1, applysubstitution s5 t2)

typeInference :: Map.Map String Scheme -> Expr -> TypeInfer Type
typeInference env e =
    do  (s, t) <- infer (TypeEnv env) e
        return (applysubstitution s t)

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
