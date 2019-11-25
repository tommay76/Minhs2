module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)

unify :: Type -> Type -> TC Subst

unify (TypeVar a)(TypeVar b) = if a == b 
  then return emptySubst
  else return (b =: (TypeVar a))

unify (Base a)(Base b) = if a == b 
  then return emptySubst
  else error "Oh lord he comin'"

unify (Prod aa ab) (Prod ba bb) = do 
  s <- unify aa ba 
  ss <- unify (substitute s ab) (substitute s bb)
  return $ s <> ss

unify (Arrow aa ab) (Arrow ba bb) = do   
  s <- unify aa ba 
  ss <- unify (substitute s ab) (substitute s bb)
  return $ s <> ss

unify (Sum aa ab) (Sum ba bb) = do   
  s <- unify aa ba 
  ss <- unify (substitute s ab) (substitute s bb)
  return $ s <> ss  

unify (TypeVar a) b = if notElem a (tv b) then
  return $ (a =: b) 
  else error "Oh no! v be in t that be whack"

unify b (TypeVar a) = unify (TypeVar a) b

unify big fInTheChat = error "There is no unity here"



generalise :: Gamma -> Type -> QType
generalise g t = foldl (\t' -> \x -> Forall x t') (Ty t) (reverse (filter (\x -> not  (elem x (tvGamma g))) (tv t)))

-- Fold instead of recursion, adding a bit of flair ;)
-- Use tv just like in unify to turn the type into a list of ids, then for each one,
-- Forall <that id> to the front of the type


inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram g [Bind f t xs e] = do 
  (e', typeP, exp)  <- inferExp g e
  return ([Bind f (Just (generalise g typeP)) xs e'], typeP, exp)
  

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)

-- Num --
inferExp g (Num i) = return ((Num i), Base Int, emptySubst) 

-- Con --
inferExp g (Con c) = case constType c of 
    Just t -> do 
      t' <- unquantify t
      return (Con c, t', emptySubst)
    Nothing       -> typeError $ NoSuchConstructor c 

-- Prim --
inferExp g (Prim o) = do 
  t' <- unquantify (primOpType o)
  return (Prim o, t', emptySubst)

-- App --
inferExp g (App e1 e2) = do
  (e1', type1, subs1) <- inferExp g e1 
  (e2', type2, subs2) <- inferExp (substGamma subs1 g) e2
  aFresh              <- fresh
  u                   <- unify (substitute subs2 type1) (Arrow type2 aFresh)
  return (App (allTypes (substQType (u <> subs2)) e1') e2', (substitute u aFresh) , (u <> subs2 <> subs1))
  
-- If --
inferExp g (If e e1 e2) = do
  (e', typeB, subsB) <- inferExp g e
  u                  <- unify typeB (Base Bool)
  case substitute (subsB <> u) typeB of
    Base Bool -> do
      (e1', type1, subs1) <- inferExp (substGamma (u <> subsB) g) e1
      (e2', type2, subs2) <- inferExp (substGamma (subs1 <> u <> subsB) g) e2
      u'                  <- unify (substitute subs2 type1) type2
      return ((If e' e1' e2'), substitute u' type2, u' <> subs2 <> subs1 <> u <> subsB) 
    t                     -> typeError $ TypeMismatch (Base Bool) t

-- Case --
-- Note: this is the only case you need to handle for case expressions
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do 
  (eE, typeE, subsE) <- inferExp g e                        -- Base exp
  a1                  <- fresh                                   --  {x : al}
  let g1 = E.add g (x, Ty a1)                                    --  T U {x : al}         > inL stuff
  (e1', type1, subs1)  <- inferExp (substGamma subsE g1) e1      --  t(T U {x : al})  
  a2                 <- fresh                                         --
  let g2 = E.add g (y, Ty a2)                                         --  > inR stuff
  (e2', type2, subs2) <- inferExp (substGamma ( subs1 <> subsE) g2) e2--
  u                  <- unify (substitute (subs2 <> subs1 <> subsE) (Sum a1 a2)) (substitute (subs2 <> subs1) typeE)  --  > Unification
  u'                  <- unify (substitute (u <> subs2) type1) (substitute u type2)                                   -- 
  return (Case eE [Alt "Inl" [x] e1', Alt "Inr" [y] e2'], substitute (u' <> u) type2, u' <> u <> subs2 <> subs1 <> subsE)
-- inferExp g (Case e _) = typeError MalformedAlternatives

-- recfun -- 
-- inferExp g (Recfun (Bind id t ids e)) = do
--   a1 <- fresh 
--   a2 <- fresh
--   -- g1 <- bindFunction  g ids    --  xs:a2
--   let g2 = E.addAll g1 [(id, Ty a2), (ids, Ty a1)] --  f: a1
--   (e', type', subs')  <- inferExp g2 e
--   u <- unify (substitute subs' a2) (Arrow  (substitute subs' a1) type')
--   return (Recfun (Bind id t ids e'),substitute u type', u <> subs')

-- inferExp g (Recfun bind) = do

-- Let Bind -- 
-- inferExp g (Let binds e) = do
--   (e1', type1, subs1) <- bindFunc g binds
--   (e2', type2, subs2) <- inferExp (type1 <> g <> (generalise (1 <> tv g) type1)) e2
--   return ((Let e1' e2'), type2, subs2 <> subs1)


inferExp g _ = error "Implement me!"


-- bindFunc :: Gamma -> [Bind] -> TC ([Bind], Gamma, Subst)

bindFunction :: Gamma -> [Id] -> TC Gamma
bindFunction g [] = return $ g 
bindFunction g (x:xs) = do 
  alpha <- fresh
  bindFunction (E.add g (x, Ty alpha)) xs

bindFunc _ _ = error "Implement me!"
