{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- CFAE AST and Type Definitions

data CFAE where
  Num :: Int -> CFAE
  Plus :: CFAE -> CFAE -> CFAE
  Minus :: CFAE -> CFAE -> CFAE
  Lambda :: String -> CFAE -> CFAE
  App :: CFAE -> CFAE -> CFAE
  Id :: String -> CFAE
  If0 :: CFAE -> CFAE -> CFAE -> CFAE
  deriving (Show,Eq)

type Env = [(String,CFAE)]

evalDynCFAE :: Env -> CFAE -> (Maybe CFAE)
evalDynCFAE env (Num x) = return (Num x)
evalDynCFAE env (Plus l r) = do { 
  (Num l') <- (evalDynCFAE env l);
  (Num r') <- (evalDynCFAE env r);
  return (Num (l'+ r')) 
}
evalDynCFAE env (Minus l r) = do { 
  (Num l') <- (evalDynCFAE env l);
  (Num r') <- (evalDynCFAE env r);
  return (Num (l'- r')) 
}
evalDynCFAE env (Lambda i b) = return (Lambda i b)
evalDynCFAE env (App f a) = do { 
  (Lambda i b) <- (evalDynCFAE env f);
  a' <- (evalDynCFAE env a);
  evalDynCFAE ((i,a'):env) b 
}
evalDynCFAE env (Id id) = do { 
  v <- (lookup id env);
  return v 
}
evalDynCFAE env (If0 c t e) = do { 
  (Num c') <- (evalDynCFAE env c);
  if c'==0 then (evalDynCFAE env t) else (evalDynCFAE env e) 
}

data CFAEValue where
  NumV :: Int -> CFAEValue
  ClosureV :: String -> CFAE -> Env' -> CFAEValue
  deriving (Show,Eq)

type Env' = [(String,CFAEValue)]

evalStatCFAE :: Env' -> CFAE -> (Maybe CFAEValue)
evalStatCFAE env (Num x) = return (NumV x)
evalStatCFAE env (Plus l r) = do { 
  (NumV l') <- (evalStatCFAE env l);
  (NumV r') <- (evalStatCFAE env r);
  return (NumV (l'+ r')) 
}
evalStatCFAE env (Minus l r) = do { 
  (NumV l') <- (evalStatCFAE env l);
  (NumV r') <- (evalStatCFAE env r);
  return (NumV (l'- r')) 
}
evalStatCFAE env (Lambda i b) = return (ClosureV i b env)
evalStatCFAE env (App f a) = do { 
  (ClosureV i b env) <- (evalStatCFAE env f);
  a' <- (evalStatCFAE env a);
  evalStatCFAE ((i,a'):env) b 
}
evalStatCFAE env (Id id) = do { 
  v <- (lookup id env);
  return v 
}
evalStatCFAE env (If0 c t e) = do { 
  (NumV c') <- (evalStatCFAE env c);
  if c'==0 then (evalStatCFAE env t) else (evalStatCFAE env e) 
}

data CFBAE where
  Num' :: Int -> CFBAE
  Plus' :: CFBAE -> CFBAE -> CFBAE
  Minus' :: CFBAE -> CFBAE -> CFBAE
  Lambda' :: String -> CFBAE -> CFBAE
  App' :: CFBAE -> CFBAE -> CFBAE
  Bind' :: String -> CFBAE -> CFBAE -> CFBAE
  Id' :: String -> CFBAE
  If0' :: CFBAE -> CFBAE -> CFBAE -> CFBAE
  deriving (Show,Eq)

elabCFBAE :: CFBAE -> CFAE
elabCFBAE (Num' x) = Num x
elabCFBAE (Plus' l r) = Plus (elabCFBAE l) (elabCFBAE r)
elabCFBAE (Minus' l r) = Minus (elabCFBAE l) (elabCFBAE r)
elabCFBAE (Lambda' i b) = Lambda i (elabCFBAE b)
elabCFBAE (App' f a) = App (elabCFBAE f) (elabCFBAE a)
elabCFBAE (Bind' i v b) = App (Lambda i (elabCFBAE b)) (elabCFBAE v)
elabCFBAE (Id' id) = Id id
elabCFBAE (If0' c t e) = If0 (elabCFBAE c) (elabCFBAE t) (elabCFBAE e)

evalCFBAE :: Env' -> CFBAE -> (Maybe CFAEValue)
evalCFBAE env expr = evalStatCFAE env $ elabCFBAE expr



