{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Arrow.Effect where
-- base
import GHC.Exts (Constraint)
import Prelude (($), flip , (.))
import qualified Control.Arrow
import qualified Control.Category
import qualified Prelude


-- effect-monad
import Control.Effect hiding (Unit, Plus, Inv)
import qualified Control.Effect as Effect

-- constraints
import Data.Constraint
import Data.Constraint.Forall

-- TODO why is this not in effect-monad?
class Effect m => FunctorEffect (m :: k -> * -> *) where
  fmap :: (a -> b) -> m f a -> m f b
  (<$>) :: (a -> b) -> m f a -> m f b
  (<$>) = fmap

-- type family RightUnitLaw (cat :: k -> * -> * -> *) :: (k -> Constraint) where
--   RightUnitLaw cat f = (Plus cat (Unit cat) f ~ f)
-- TODO If these constraints work, send as a PR to effect-monad
class
	-- ( Forall (RightUnitLaw cat)
  --, forall f     . Plus cat f (Unit cat) ~ f
  --, forall f g h . Plus cat f (Plus cat g h) ~ Plus cat (Plus cat f g) h
  --) => 
  CategoryEffect (cat :: k -> * -> * -> *) where
  type Unit cat :: k
  type Plus cat (f :: k) (g :: k) :: k
  type Inv cat (f :: k) (g :: k) :: Constraint
  type Inv cat f g = ()

  id :: cat (Unit cat) a a
  (>>>) :: Inv cat f g => cat f a b -> cat g b c -> cat (Plus cat f g) a c

  leftUnit :: Dict (cat (Plus cat (Unit cat) f) a b ~ cat f a b)
	-- leftUnit :: Plus cat (Unit cat) f ~ f)

class CategoryEffect a => ArrowEffect (a :: k -> * -> * -> *) where
  arr :: (b -> c) -> a (Unit a) b c
  first :: a f b c -> a f (b, d) (c, d)

class ArrowFeedback a where
  feedback :: d -> a (b, d) (c, d) -> a b c

newtype Fun (k :: ()) a b = Fun { unFun :: a -> b }

instance CategoryEffect Fun where
  type Unit Fun = '()
  type Plus Fun f g = '()
  type Inv Fun f g = ()
  id = Fun Prelude.id
  --Fun f >>> Fun g = Fun $ f Prelude.(>>>) g TODO How to make this work?
  Fun f >>> Fun g = Fun $ g . f
  leftUnit = Dict

instance ArrowEffect Fun where
  arr f = Fun f
  first (Fun f) = Fun $ Control.Arrow.first f

newtype Kleisli m f a b = Kleisli { runKleisli :: a -> m f b }

instance Effect m => CategoryEffect (Kleisli m) where
  type Unit (Kleisli m) = Effect.Unit m
  type Plus (Kleisli m) f g = Effect.Plus m f g
  type Inv (Kleisli m) f g = Effect.Inv m f g
  id = Kleisli return
  Kleisli f >>> Kleisli g = Kleisli $ \b -> f b >>= g

instance (FunctorEffect m, Effect m) => ArrowEffect (Kleisli m) where
  arr f = Kleisli $ return . f
  first (Kleisli f) = Kleisli $ \(b, d) -> ( , d) <$> f b

data MSF m f a b = MSF (a -> m f (b, MSF m f a b))

-- TODO Here and later: Use Kmett's type level constraints trickery
-- to define a type level monoid constraint for m
instance (FunctorEffect m, Effect m) => CategoryEffect (MSF m) where
  type Unit (MSF m) = Effect.Unit m
  type Plus (MSF m) f g = Effect.Plus m f g
  type Inv (MSF m) f g = Effect.Inv m f g
  id = go where go = MSF $ \a -> return (a, go)
  MSF f >>> MSF g = MSF $ \a -> do
    (b, f') <- f a
    (\(c, g') -> (c, f' >>> g')) <$> g b

instance (FunctorEffect m, Effect m) => ArrowEffect (MSF m) where
  arr f = go where go = MSF $ \a -> return (f a, go)
  first (MSF f) = MSF $ \(b, d) -> flip fmap (f b) $ \(c, f') -> ((c, d), first f')
    --(c, f') <- f b
    --return ((c, d), first f')

instance (FunctorEffect m, Effect m) => ArrowFeedback (MSF m f) where
  feedback d (MSF f) = go d
    where
      go d = MSF $ \b -> flip fmap (f (b, d)) $ \((c', d'), f') -> (c', go d')


data Fusion m f a b where
  Fusion :: s -> (a -> s -> m f (b, s)) -> Fusion m f a b

instance (FunctorEffect m, Effect m) => CategoryEffect (Fusion m) where
  type Unit (Fusion m) = Effect.Unit m
  type Plus (Fusion m) f g = Effect.Plus m f g
  type Inv (Fusion m) f g = Effect.Inv m f g
  id = Fusion () $ \a () -> return (a, ())
  Fusion s0 f >>> Fusion t0 g = Fusion (s0, t0) $ \a (s, t) -> do
    (b, s') <- f a s
    (\(c, t') -> (c, (s', t'))) <$> g b t

instance (FunctorEffect m, Effect m)  => ArrowEffect (Fusion m) where
  arr f = Fusion () $ \a () -> return (f a, ())
  first (Fusion s0 f) = Fusion s0 $ \(a, c) s -> (\(b, s') -> ((b, c), s')) <$> f a s
