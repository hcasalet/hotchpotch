import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

type Var = String
type Substitutable = Map.Map String Type

data Const = CInt Integer
           | CBool Bool
           deriving (Show, Eq, Ord)

-- Type variable
data Type    =  TVar Var
             |  TCon String
             |  TFun Type Type
             |  TList [Var]
             deriving (Show, Eq, Ord)

data Scheme = Forall [Var] Type

-- Type environment variable
newtype TypeEnv = TypeEnv (Map.Map Var Scheme)
extend :: TypeEnv -> (Var, Scheme) -> TypeEnv
extend (TypeEnv env) (x, s) = TypeEnv $ Map.insert x s env

-- Substitution
class Subst a where
    applysubstitution  ::  Substitutable -> a -> a
    freetypevariable    ::  a -> Set.Set String

instance Subst Type where
    applysubstitution _ (TCon a)      = TCon a
    applysubstitution s (TVar n)      =  case Map.lookup n s of
                                            Nothing  -> TVar n
                                            Just t   -> t
    applysubstitution s (TFun t1 t2)  = TFun (applysubstitution s t1) (applysubstitution s t2)
    freetypevariable (TVar n)         =  Set.singleton n
    freetypevariable TCon{}           =  Set.empty
    freetypevariable (TFun t1 t2)     =  freetypevariable t1 `Set.union` freetypevariable t2

instance Subst Scheme where
    freetypevariable (Forall vars t)         = freetypevariable t `Set.difference` (Set.fromList vars)
    applysubstitution s (Forall vars t)      = Forall vars $ applysubstitution s' t
                                 where s' = foldr Map.delete s vars

instance Subst a => Subst [a] where
    freetypevariable l   =  foldr Set.union Set.empty (map freetypevariable l)
    applysubstitution s  =  map (applysubstitution s)

instance Subst TypeEnv where
    freetypevariable (TypeEnv env)     =  freetypevariable $ Map.elems env
    applysubstitution s (TypeEnv env)  =  TypeEnv $ Map.map (applysubstitution s) env

emptySubstitutable  ::  Substitutable
emptySubstitutable  =   Map.empty

mergeSubstitutable  :: Substitutable -> Substitutable -> Substitutable
mergeSubstitutable s1 s2   = (Map.map (applysubstitution s1) s2) `Map.union` s1

-- Generalization
generalize        ::  TypeEnv -> Type -> Scheme
generalize env t  =   Forall vars t
    where vars = Set.toList ((freetypevariable t) `Set.difference` (freetypevariable env))

type TypeInfer a = ExceptT String (ReaderT TypeInferEnv (StateT TypeInferState IO)) a
newTypeVar :: String -> TypeInfer Type
newTypeVar prefix =
        do  s <- get
            put s{inferenceSupply = inferenceSupply s + 1}
            return (TVar  (prefix ++ show (inferenceSupply s)))

-- Instantiation
instantiate :: Scheme -> TypeInfer Type
instantiate (Forall vars t) = do  nvars <- mapM (\ _ -> newTypeVar "a") vars
                                  let s = Map.fromList (zip vars nvars)
                                  return $ applysubstitution s t

-- Unification
unify :: Type -> Type -> TypeInfer Substitutable
unify (TCon a) (TCon b) | a == b      = return emptySubstitutable
unify (TVar u) t                      =  bind u t
unify t (TVar u)                      =  bind u t
unify (TFun l r) (TFun l' r')         =  do  s1 <- unify l l'
                                             s2 <- unify (applysubstitution s1 r) (applysubstitution s1 r')
                                             return (s1 `mergeSubstitutable` s2)
unify t1 t2                           =  throwError $ "Type "  ++ show t1 ++
                                       " and type " ++ show t2 ++ " do not unify."

occursCheck ::  Subst a => String -> a -> Bool
occursCheck a t = a `Set.member` freetypevariable t

bind :: String -> Type -> TypeInfer Substitutable
bind u t  | t == TVar u           =  return emptySubstitutable
          | occursCheck u t       =  throwError $ "Type " ++ u ++ " does not occur in scheme " ++ show t ++ "."
          | otherwise             =  return (Map.singleton u t)

-- Expressions to do type inference on
data Expr     =  Var Var
              |  Con Const
              |  App Expr Expr
              |  Lam String Expr
              |  Let String Expr Expr
              |  If Expr Expr Expr
              deriving (Show, Eq, Ord)

data TypeInferEnv = TypeInferEnv  {}
data TypeInferState = TypeInferState { inferenceSupply :: Int,
         inferenceSubstitutable :: Substitutable}
runTypeInfer :: TypeInfer a -> IO (Either String a, TypeInferState)
runTypeInfer t =
      do (res, st) <- runStateT (runReaderT (runExceptT t) initTIEnv) initTIState
         return (res, st)
    where initTIEnv = TypeInferEnv{}
          initTIState = TypeInferState{inferenceSupply = 0,
                                inferenceSubstitutable = Map.empty}

infer        ::  TypeEnv -> Expr -> TypeInfer (Substitutable, Type)
infer (TypeEnv env) (Con l) =
    case l of
        CInt n -> return (emptySubstitutable, TCon "Int")
        CBool n -> return (emptySubstitutable, TCon "Bool")
infer (TypeEnv env) (Var n) =
    case Map.lookup n env of
        Nothing     ->  throwError $ "Variable " ++ n ++ " is unbound."
        Just sigma  ->  do t <- instantiate sigma
                           return (emptySubstitutable, t)
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
        return (s3 `mergeSubstitutable` s2 `mergeSubstitutable` s1, applysubstitution s3 tv)
infer env (Let x e1 e2) =
    do  (s1, t1) <- infer env e1
        let    t' = generalize (applysubstitution s1 env) t1
        (s2, t2) <- infer ((applysubstitution s1 env) `extend` (x, t')) e2
        return (s1 `mergeSubstitutable` s2, t2)
infer env (If e1 e2 e3) =
    do  (s1, t1) <- infer env e1
        (s2, t2) <- infer env e2
        (s3, t3) <- infer env e3
        s4 <- unify t1 (TCon "Bool")
        s5 <- unify t2 t3
        return (s5 `mergeSubstitutable` s4 `mergeSubstitutable` s3 `mergeSubstitutable` s2 `mergeSubstitutable` s1, applysubstitution s5 t2)

typeInference :: Map.Map String Scheme -> Expr -> TypeInfer Type
typeInference env e =
    do  (s, t) <- infer (TypeEnv env) e
        return (applysubstitution s t)

-- $$$$$$$$$$$$$$$$$$$
-- Test Cases
-- $$$$$$$$$$$$$$$$$$$

-- (Lambda x).25 => TFun (TVar "a0") (TCon "Int")
e1  = Lam "x" (Con (CInt 25))

-- (Lambda x).False => TFun (TVar "a0") (TCon "Bool")
e2  = Lam "x" (Con (CBool False))

-- App (lambda x).True 15 => type: TCon "Bool"
e3  = App (Lam "x" (Con (CBool True))) (Con (CInt 15))

-- App (lambda x).False 25 => type: TCon "Bool"
e4  = App (Lam "x" (Con (CInt 25))) (Var "y")

-- let y = (lambda x).0 y => type: TFun (TVAR "a1") (TCon "Int")
e5  =  Let "y" (Lam "x" (Con (CInt 0)))
        (Var "y")

-- (lambda m).(let x m (let y x(true)) y)  => TFun (TFun (TCon "Bool") (TVar "a1")) (TVar "a1")
e6  =  Lam "m" (Let "x" (Var "m")
            (Let "y" (App (Var "x") (Con (CBool True)))
                (Var "y")))

-- If e1 then e2 else e3 => TCon "Int" (e2 (or e3))
e7  = If (Con (CBool True))
        (App (Lam "x" (Con (CInt 15))) (Con (CInt 25)))
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
