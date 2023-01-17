{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Indexed.Functor where

import Data.Kind (Type)

infixr 0 ~>
type f ~> g = forall x. f x -> g x

class IFunctor f where
    imap :: (a ~> b) -> f a ~> f b

class IFunctor f => IApplicative f where
    ireturn :: a ~> f a

class IApplicative m => IMonad m where
    ibind :: (a ~> m b) -> m a ~> m b

class IMonad m => IMonadFail m where
    fail :: String -> m a ix

data At :: Type -> k -> k -> Type where
    At :: a -> At a k k

(>>=) :: IMonad (m :: (x -> Type) -> x -> Type) => m a ix -> (a ~> m b) -> m b ix
m >>= f = ibind f m

(>>) :: IMonad (m :: (x -> Type) -> x -> Type) => m (At a j) i -> m b j -> m b i
m >> f = ibind (\(At _) -> f) m
