{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Network.Redesign.T1 where

import Data.Kind (Type)
import Data.Singletons
import Indexed.Functor as I
import Network.Redesign.Core as Core

data
  K ps ::
    (IsPipelined, Queue ps, ps) ->
    (IsPipelined, Queue ps, ps) ->
    Type
  where
  K :: Message ps st st' -> K ps '(pl, que, st) '(pl, que, st')

type family EST que st st'' where
  EST Empty st st'' = st''
  EST _ st st'' = st

data
  C ps ::
    (IsPipelined, Queue ps, ps) ->
    (IsPipelined, Queue ps, ps) ->
    Type
  where
  C ::
    Message ps st' stNext ->
    C ps '(pl, Tr st' st'' <| que, st) '(pl, Tr stNext st'' <| que, EST que st st'')

data
  C1 ps ::
    (IsPipelined, Queue ps, ps) ->
    (IsPipelined, Queue ps, ps) ->
    Type
  where
  C1 ::
    Message ps st' st'' ->
    C1 ps '(pl, Tr st' st'' <| que, st) '(pl, que, EST que st st'')

type Peer ::
  forall ps ->
  PeerRole ->
  (Type -> Type) ->
  ((IsPipelined, Queue ps, ps) -> Type) ->
  (IsPipelined, Queue ps, ps) ->
  Type
data Peer ps pr m q k where
  SReturn :: q k -> Peer ps pr m q k
  SEffect :: m (Peer ps pr m q k) -> Peer ps pr m q k
  SYield ::
    forall ps pr pl (st :: ps) (st' :: ps) m q.
    ( SingI st,
      SingI st',
      ActiveState st
    ) =>
    WeHaveAgencyProof pr st ->
    Message ps st st' ->
    Peer ps pr m q '(pl, Empty, st') ->
    Peer ps pr m q '(pl, Empty, st)
  SAwait ::
    forall ps pr pl (st :: ps) m q.
    ( SingI st,
      ActiveState st
    ) =>
    TheyHaveAgencyProof pr st ->
    (K ps '(pl, Empty, st) I.~> Peer ps pr m q) ->
    Peer ps pr m q '(pl, Empty, st)
  SYieldPipelined ::
    forall ps pr que (st :: ps) (st' :: ps) (st'' :: ps) m q.
    ( SingI st,
      SingI st',
      ActiveState st
    ) =>
    WeHaveAgencyProof pr st ->
    Message ps st st' ->
    Peer ps pr m q '(Pipelined, que |> Tr st' st'', st'') ->
    Peer ps pr m q '(Pipelined, que, st)
  SCollect ::
    forall ps pr que (st :: ps) (st' :: ps) (st'' :: ps) m q.
    ( SingI st',
      ActiveState st'
    ) =>
    TheyHaveAgencyProof pr st' ->
    (C ps '(Pipelined, Tr st' st'' <| que, st) I.~> Peer ps pr m q) ->
    Peer ps pr m q '(Pipelined, Tr st' st'' <| que, st)
  SCollectDone ::
    forall ps pr que (st :: ps) (st' :: ps) m q.
    Peer ps pr m q '(Pipelined, que, st') ->
    Peer ps pr m q '(Pipelined, Tr st st <| que, st')
  SCollectDoneF ::
    forall ps pr que (st :: ps) (st' :: ps) (st'' :: ps) m q.
    ( SingI st',
      ActiveState st'
    ) =>
    TheyHaveAgencyProof pr st' ->
    (C1 ps '(Pipelined, Tr st' st'' <| que, st) I.~> Peer ps pr m q) ->
    Peer ps pr m q '(Pipelined, Tr st' st'' <| que, st)

instance Functor m => IFunctor (Peer ps pr m) where
  imap f (SReturn q) = SReturn (f q)
  imap f (SEffect m) = SEffect (fmap (imap f) m)
  imap f (SYield whap msg pr) = SYield whap msg (imap f pr)
  imap f (SAwait thap cont) = SAwait thap (imap f . cont)
  imap f (SYieldPipelined whap msg pr) = SYieldPipelined whap msg (imap f pr)
  imap f (SCollect thap cont) = SCollect thap (imap f . cont)
  imap f (SCollectDone pr) = SCollectDone (imap f pr)
  imap f (SCollectDoneF thap cont) = SCollectDoneF thap (imap f . cont)

instance Functor m => IApplicative (Peer ps pr m) where
  ireturn = SReturn

instance Functor m => IMonad (Peer ps pr m) where
  ibind f (SReturn q) = f q
  ibind f (SEffect m) = SEffect (fmap (ibind f) m)
  ibind f (SYield whap msg pr) = SYield whap msg (ibind f pr)
  ibind f (SAwait thap cont) = SAwait thap (ibind f . cont)
  ibind f (SYieldPipelined whap msg pr) = SYieldPipelined whap msg (ibind f pr)
  ibind f (SCollect thap cont) = SCollect thap (ibind f . cont)
  ibind f (SCollectDone pr) = SCollectDone (ibind f pr)
  ibind f (SCollectDoneF thap cont) = SCollectDoneF thap (ibind f . cont)

--   SReturn :: q k -> Peer ps pr m q k
sReturn :: a -> Peer ps pr m (At a i) i
sReturn a = SReturn (At a)

--   SEffect :: m (Peer ps pr m q k) -> Peer ps pr m q k
effect :: Functor m => m a -> Peer ps pr m (At a st) st
effect ma = SEffect (fmap (SReturn . At) ma)

-------------------------- client fun
sYield ::
  (SingI st, SingI st', ActiveState st, StateAgency st ~ ClientAgency) =>
  Message ps st st' ->
  Peer ps AsClient m (At () '(pl, Empty, st')) '(pl, Empty, st)
sYield msg = SYield ReflClientAgency msg (SReturn (At ()))

sAwait ::
  (SingI st, ActiveState st, StateAgency st ~ ServerAgency) =>
  Peer ps AsClient m (K ps '(pl, Empty, st)) '(pl, Empty, st)
sAwait = SAwait ReflServerAgency SReturn

sYieldPipelined ::
  forall ps (st'' :: ps) st st' m que.
  (SingI st, SingI st', ActiveState st, StateAgency st ~ ClientAgency) =>
  Message ps st st' ->
  Peer ps AsClient m (At () '(Pipelined, que |> Tr st' st'', st'')) '(Pipelined, que, st)
sYieldPipelined msg = SYieldPipelined ReflClientAgency msg (SReturn (At ()))

sCollect ::
  (SingI st', ActiveState st', StateAgency st' ~ ServerAgency) =>
  Peer ps AsClient m (C ps '(Pipelined, Tr st' st'' <| que, st)) '(Pipelined, Tr st' st'' <| que, st)
sCollect = SCollect ReflServerAgency SReturn

sCollectDone :: Peer ps pr m (At () '(Pipelined, que, st')) '(Pipelined, Tr st st <| que, st')
sCollectDone = SCollectDone (SReturn $ At ())

sCollectDoneF ::
  (SingI st', ActiveState st', StateAgency st' ~ ServerAgency) =>
  Peer ps AsClient m (C1 ps '(Pipelined, Tr st' st'' <| que, st)) '(Pipelined, Tr st' st'' <| que, st)
sCollectDoneF = SCollectDoneF ReflServerAgency SReturn

-- ---------------------------- example
data PingPong where
  StIdle :: PingPong
  StBusy :: PingPong
  StDone :: PingPong
  A :: PingPong
  B :: PingPong
  P :: PingPong

data SPingPong (st :: PingPong) where
  SingIdle :: SPingPong StIdle
  SingBusy :: SPingPong StBusy
  SingDone :: SPingPong StDone
  SingA :: SPingPong A
  SingB :: SPingPong B
  SingP :: SPingPong P

deriving instance Show (SPingPong st)

type instance Sing = SPingPong

instance SingI StIdle where
  sing = SingIdle

instance SingI StBusy where
  sing = SingBusy

instance SingI StDone where
  sing = SingDone

instance SingI A where
  sing = SingA

instance SingI B where
  sing = SingB

instance SingI P where
  sing = SingP

instance Protocol PingPong where
  data Message PingPong from to where
    MsgPing :: Message PingPong StIdle StBusy
    MsgPong :: Message PingPong StBusy StIdle
    MsgDone :: Message PingPong StIdle StDone
    MsgA :: Message PingPong StBusy P
    MsgA1 :: Message PingPong P A
    MsgAB :: Message PingPong A B
    MsgB :: Message PingPong B StIdle

  type StateAgency StIdle = ClientAgency
  type StateAgency StBusy = ServerAgency
  type StateAgency A = ClientAgency
  type StateAgency P = ServerAgency
  type StateAgency B = ServerAgency
  type StateAgency StDone = NobodyAgency

  type StateToken = SPingPong

ppClient ::
  (Functor m, IMonadFail (Peer PingPong 'AsClient m)) =>
  Peer
    PingPong
    AsClient
    m
    (At () '(Pipelined, Empty, StDone))
    '(Pipelined, Empty, StIdle)
ppClient = I.do
  sYieldPipelined MsgPing
  sYieldPipelined @_ @StIdle MsgAB
  sCollect I.>>= \case
    C MsgA ->
      sCollect I.>>= \case
        C MsgA1 -> I.do
          sCollectDone
          sCollect I.>>= \case
            C MsgB -> I.do
              sCollectDone
              sYield MsgDone
    _ -> undefined

ppClient1 ::
  (Functor m, IMonadFail (Peer PingPong 'AsClient m)) =>
  Peer
    PingPong
    AsClient
    m
    (At () '(Pipelined, Empty, StDone))
    '(Pipelined, Empty, StIdle)
ppClient1 = I.do
  sYieldPipelined @_ @A MsgPing
  sCollect I.>>= \case
    C MsgA ->
      sCollect I.>>= \case
        C MsgA1 -> I.do
          sCollectDone
          sYieldPipelined @_ @StIdle MsgAB
          sCollect I.>>= \case
            C MsgB -> I.do
              sCollectDone
              sYield MsgDone
    C MsgPong -> I.do
      -- sCollectDone
      -- sYield MsgDone
      undefined

ppClient2 ::
  (Functor m, IMonadFail (Peer PingPong 'AsClient m)) =>
  Peer
    PingPong
    AsClient
    m
    (At () '(NonPipelined, Empty, StDone))
    '(NonPipelined, Empty, StIdle)
ppClient2 = I.do
  sYield MsgPing
  sAwait I.>>= \case
    K MsgPong -> sYield MsgDone
    K MsgA ->
      sAwait I.>>= \case
        K MsgA1 -> I.do
          sYield MsgAB
          sAwait I.>>= \case
            K MsgB -> sYield MsgDone

ppClient3 ::
  (Functor m, IMonadFail (Peer PingPong 'AsClient m)) =>
  Peer
    PingPong
    AsClient
    m
    (At () '(NonPipelined, Empty, StDone))
    '(NonPipelined, Empty, StIdle)
ppClient3 = I.do
  sYield MsgPing
  sAwait I.>>= \case
    K MsgPong -> ppClient3
    K MsgA -> I.do
      K MsgA1 <- sAwait
      sYield MsgAB
      K MsgB <- sAwait
      sYield MsgDone

