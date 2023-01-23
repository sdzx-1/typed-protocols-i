{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Network.TypedProtocol.Pipelined
  ( PeerPipelined (..)
  , PeerSender (..)
  , PeerReceiver (..)
  , Outstanding
  , N (..)
  , Nat (Zero, Succ)
  , natToInt
  , unsafeIntToNat
  , fmapPeerPipelined
  ) where

import           Unsafe.Coerce (unsafeCoerce)

import           Network.TypedProtocol.Core


data PeerPipelined ps (pr :: PeerRole) (st :: ps) m a where
  PeerPipelined :: PeerSender    ps pr st Z c m a
                -> PeerPipelined ps pr st     m a

deriving instance Functor m => Functor (PeerPipelined ps (pr :: PeerRole) (st :: ps) m)

fmapPeerPipelined :: (forall c. PeerSender ps pr st Z c m a -> PeerSender ps' pr st' Z c m b)
                  -> PeerPipelined ps  pr st  m a
                  -> PeerPipelined ps' pr st' m b
fmapPeerPipelined f (PeerPipelined peer) = PeerPipelined (f peer)

data PeerSender ps (pr :: PeerRole) (st :: ps) (n :: Outstanding) c m a where

  SenderEffect   :: m (PeerSender ps pr st n c m a)
                 ->    PeerSender ps pr st n c m a

  SenderDone     :: !(NobodyHasAgency st)
                 -> a
                 -> PeerSender ps pr st Z c m a

  SenderYield    :: !(WeHaveAgency pr st)
                 -> Message    ps st st'
                 -> PeerSender ps pr st' Z c m a
                 -> PeerSender ps pr st  Z c m a

  SenderAwait    :: !(TheyHaveAgency pr st)
                 -> (forall st'. Message    ps st st'
                              -> PeerSender ps pr st' Z c m a)
                 -> PeerSender              ps pr st  Z c m a

  SenderPipeline :: !(WeHaveAgency   pr st)
                 -> Message ps st st'
                 -> PeerReceiver ps pr (st'  :: ps) (st'' :: ps) m c
                 -> PeerSender   ps pr (st'' :: ps) (S n) c m a
                 -> PeerSender   ps pr (st   :: ps)    n  c m a

  SenderCollect  :: Maybe (PeerSender ps pr (st :: ps) (S n) c m a)
                 -> (c ->  PeerSender ps pr (st :: ps)    n  c m a)
                 ->        PeerSender ps pr (st :: ps) (S n) c m a

deriving instance Functor m => Functor (PeerSender ps (pr :: PeerRole) (st :: ps) (n :: Outstanding) c m)

data PeerReceiver ps (pr :: PeerRole) (st :: ps) (stdone :: ps) m c where

  ReceiverEffect :: m (PeerReceiver ps pr st stdone m c)
                 ->    PeerReceiver ps pr st stdone m c

  ReceiverDone   :: c -> PeerReceiver ps pr stdone stdone m c

  ReceiverAwait  :: !(TheyHaveAgency pr st)
                 -> (forall st'. Message ps st st'
                              -> PeerReceiver ps pr st' stdone m c)
                 -> PeerReceiver ps pr st stdone m c


type Outstanding = N

data N = Z | S N

newtype Nat (n :: N) = UnsafeInt Int
  deriving Show via Int

data IsNat (n :: N) where
  IsZero ::          IsNat Z
  IsSucc :: Nat n -> IsNat (S n)

toIsNat :: Nat n -> IsNat n
toIsNat (UnsafeInt 0) = unsafeCoerce IsZero
toIsNat (UnsafeInt n) = unsafeCoerce (IsSucc (UnsafeInt (pred n)))

pattern Zero :: () => Z ~ n => Nat n
pattern Zero <- (toIsNat -> IsZero) where
  Zero = UnsafeInt 0

pattern Succ :: () => (m ~ S n) => Nat n -> Nat m
pattern Succ n <- (toIsNat -> IsSucc n) where
  Succ (UnsafeInt n) = UnsafeInt (succ n)

{-# COMPLETE Zero, Succ #-}

natToInt :: Nat n -> Int
natToInt (UnsafeInt n) = n

unsafeIntToNat :: Int -> Nat n
unsafeIntToNat = UnsafeInt
