{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars t     = case t of 
    TInt -> []
    TBool -> []
    ty :=> ty' -> if freeTVars ty == freeTVars ty' then freeTVars ty else freeTVars ty ++ freeTVars ty'
    TVar s -> [s]
    TList ty -> freeTVars ty

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars (Mono m)  = freeTVars m
  freeTVars (Forall tvar p) = freeTVars p L.\\ [tvar]

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar id []            = TVar id
lookupTVar id ((id', t):xs)
  | id == id'   = t
  | otherwise   = lookupTVar id xs


-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar a subs = subs L.\\ [(a, lookupTVar a subs)]

-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply sub t         = case t of
    TInt -> t
    TBool -> t
    ty :=> ty' -> apply sub ty :=> apply sub ty'
    TVar s -> lookupTVar s sub
    TList ty -> TList (apply sub ty)


-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply sub (Mono m)    = Mono (apply sub m)
  apply sub (Forall a p)  = Forall a (apply sub p)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst s id t = (id, apply s t) : helper [(id, apply s t)] s
  where
    helper :: Subst -> Subst -> Subst
    helper newS []            = []
    helper newS ((id, t):xs)  = (id, apply newS t) : helper newS xs
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st id t
  | t == TVar id            = st
  | id `elem` freeTVars t   = throw (Error ("type error: cannot unify " ++ id ++ " and " ++ show t))
  | otherwise               = extendState st id t
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2          = case t1 of
  TVar id -> unifyTVar st id t2
  TInt -> case t2 of
    TInt -> st
    TBool -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    TVar id -> unifyTVar st id t1
    TList ty -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    ty :=> ty' -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
  TBool -> case t2 of
    TInt -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    TBool -> st
    TVar id -> unifyTVar st id t1
    TList ty -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    ty :=> ty' -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
  TList ty -> case t2 of
    TInt -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    TBool -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    TVar id -> unifyTVar st id t1
    TList ty' -> unify st ty ty'
    ty2 :=> ty3 -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
  tyL :=> tyR -> case t2 of
    TInt -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    TBool -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    TVar id -> unifyTVar st id t1
    TList ty2 -> throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))
    tyL' :=> tyR' -> st'
      where
        InferState sub cnt = unify st tyL tyL'
        (tyR2, tyR'2) = (apply sub tyR, apply sub tyR')
        st' = unify (InferState sub cnt) tyR2 tyR'2

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _)          = (st, TInt)
infer st _   (EBool _)         = (st, TBool)
infer st gamma (EVar x)        = (st', ty')
  where
    ty          = lookupVarType x gamma
    (cnt, ty')  = instantiate (stCnt st) ty
    st'         = InferState (stSub st) cnt
infer st gamma (ELam x body)   = (st', tX' :=> tBody)
  where
    (st1, tX)     = (InferState (stSub st) ((stCnt st) + 1), freshTV (stCnt st))
    gamma'        = extendTypeEnv x (Mono tX) gamma
    (st', tBody)  = infer st1 gamma' body
    tX'           = apply (stSub st') tX
infer st gamma (EApp e1 e2)      = (st', tX')
  where
    (st1, tF) = infer st gamma e1
    gamma'    = apply (stSub st1) gamma
    (st2, tA) = infer st1 gamma' e2
    (st3, tX) = (InferState (stSub st2) (stCnt st2 + 1), freshTV (stCnt st2))
    st'       = unify st3 tF (tA :=> tX)
    tX'       = apply (stSub st') tX
infer st gamma (ELet x e1 e2)  = (st', tX')
  where
    (st1, tE1)  = infer st gamma e1
    gamma'      = apply (stSub st1) gamma
    tE2         = generalize gamma' tE1
    gamma''     = extendTypeEnv x tE2 gamma'
    (st', tX')  = infer st1 gamma'' e2
infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = helper tVars
  where
    tVars  = freeTVars t L.\\ freeTVars gamma
    helper :: [TVar] -> Poly
    helper [] = Mono t
    helper xs = Forall (head xs) (helper (tail xs))
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n s = helper (InferState [] n) s
  where
    helper :: InferState -> Poly -> (Int, Type)
    helper st s = case s of
      Mono t -> (stCnt st, apply (stSub st) t)
      Forall id s -> helper (InferState (stSub (extendState st id (freshTV (stCnt st)))) (stCnt st + 1)) s
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Mono $ TVar "p" :=> TVar "p" :=> TBool)
  , ("!=",   Mono $ TVar "p0" :=> TVar "p0" :=> TBool)
  , ("<",    Mono $ TInt :=> TInt :=> TBool)
  , ("<=",   Mono $ TInt :=> TInt :=> TBool)
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   Mono $ TBool)
  -- lists: 
  , ("[]",   Mono $ TVar "p1" :=> TList (TVar "p1"))
  , (":",    Mono $ TVar "p2" :=> TList (TVar "p2") :=> TList (TVar "p2") )
  , ("head", Mono $ TList (TVar "p3") :=> TVar "p3")
  , ("tail", Mono $ TList (TVar "p4") :=> TList (TVar "p4"))
  ]
