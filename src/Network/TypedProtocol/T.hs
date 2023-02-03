{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Network.TypedProtocol.T where

import Control.Monad (forever)
import Data.Kind (Type)
import Indexed.Functor
import Indexed.Functor as I
import Network.TypedProtocol.Core hiding (effect)
import Network.TypedProtocol.Pipelined

data K ps :: (N, st) -> (N, st) -> Type where
  K :: Message ps st st' -> K ps '(n, st) '(n, st')

data PS ps pr c m q (k :: (N, st)) where
  SReturn :: q k -> PS ps pr c m q k
  SEffect :: m (PS ps pr c m q k) -> PS ps pr c m q k
  SYield ::
    (WeHaveAgency pr st) ->
    Message ps st st' ->
    PS ps pr c m q '(Z, st') ->
    PS ps pr c m q '(Z, st)
  SAwait ::
    TheyHaveAgency pr st ->
    (K ps '(Z, st) ~> PS ps pr c m q) ->
    PS ps pr c m q '(Z, st)
  SPipeline ::
    WeHaveAgency pr st ->
    Message ps st st' ->
    PeerReceiver ps pr st' st'' m c ->
    PS ps pr c m q '(S n, st'') ->
    PS ps pr c m q '(n, st)
  SCollect ::
    (At c '(n, st) ~> PS ps pr c m q) ->
    PS ps pr c m q '(S n, st)

instance Functor m => IFunctor (PS ps pr c m) where
  imap f (SReturn q) = SReturn (f q)
  imap f (SEffect mq) = SEffect (fmap (imap f) mq)
  imap f (SYield wha msg ps) = SYield wha msg (imap f ps)
  imap f (SAwait tha cont) = SAwait tha (imap f . cont)
  imap f (SPipeline wha msg pRecv ps) = SPipeline wha msg pRecv (imap f ps)
  imap f (SCollect ps) = SCollect (imap f . ps)

instance Functor m => IApplicative (PS ps pr c m) where
  ireturn = SReturn

instance Functor m => IMonad (PS ps pr c m) where
  ibind f (SReturn q) = f q
  ibind f (SEffect mq) = SEffect (fmap (ibind f) mq)
  ibind f (SYield wha msg ps) = SYield wha msg (ibind f ps)
  ibind f (SAwait tha cont) = SAwait tha (ibind f . cont)
  ibind f (SPipeline wha msg pRecv ps) = SPipeline wha msg pRecv (ibind f ps)
  ibind f (SCollect ps) = SCollect (ibind f . ps)

sReturn :: a -> PS ps pr c m (At a i) i
sReturn a = SReturn (At a)

effect :: Functor m => m a -> PS ps pr c m (At a st) st
effect ma = SEffect (fmap (SReturn . At) ma)

sYield ::
  WeHaveAgency pr st ->
  Message ps st st' ->
  PS ps pr c m (At () '(Z, st')) '(Z, st)
sYield wha msg = SYield wha msg (SReturn (At ()))

sAwait ::
  TheyHaveAgency pr st ->
  PS ps pr c m (K ps '(Z, st)) '(Z, st)
sAwait tha = SAwait tha SReturn

sPipeline ::
  WeHaveAgency pr st ->
  Message ps st st' ->
  PeerReceiver ps pr st' st'' m c ->
  PS ps pr c m (At () '(S n, st'')) '(n, st)
sPipeline wha msg precv =
  SPipeline wha msg precv (SReturn (At ()))

sCollect :: PS ps pr c m (At c '(n, st)) '(S n, st)
sCollect = SCollect SReturn

data PingPong where
  StIdle :: PingPong
  StBusy :: PingPong
  StDone :: PingPong

instance Protocol PingPong where
  data Message PingPong from to where
    MsgPing :: Message PingPong StIdle StBusy
    MsgPong :: Message PingPong StBusy StIdle
    MsgDone :: Message PingPong StIdle StDone

  data ClientHasAgency st where
    TokIdle :: ClientHasAgency StIdle

  data ServerHasAgency st where
    TokBusy :: ServerHasAgency StBusy

  data NobodyHasAgency st where
    TokDone :: NobodyHasAgency StDone

  exclusionLemma_ClientAndServerHaveAgency TokIdle tok = case tok of {}
  exclusionLemma_NobodyAndClientHaveAgency TokDone tok = case tok of {}
  exclusionLemma_NobodyAndServerHaveAgency TokDone tok = case tok of {}

ppClientPeerSender ::
  Functor m =>
  PS PingPong AsClient c m (At () '(Z, StDone)) '(Z, StIdle)
ppClientPeerSender = I.do
  sYield (ClientAgency TokIdle) MsgPing
  K v <- sAwait (ServerAgency TokBusy)
  case v of
    MsgPong -> sYield (ClientAgency TokIdle) MsgDone

ppSender ::
  Functor m =>
  PS PingPong AsClient () m (At () '(Z, StDone)) '(Z, StIdle)
ppSender = I.do
  sYield (ClientAgency TokIdle) MsgPing
  K v <- sAwait (ServerAgency TokBusy)
  case v of
    MsgPong -> I.do
      sPipeline (ClientAgency TokIdle) MsgPing (ReceiverAwait (ServerAgency TokBusy) $ \MsgPong -> ReceiverDone ())
      sPipeline (ClientAgency TokIdle) MsgPing (ReceiverAwait (ServerAgency TokBusy) $ \MsgPong -> ReceiverDone ())
      sCollect
      sCollect
      sPipeline (ClientAgency TokIdle) MsgPing (ReceiverAwait (ServerAgency TokBusy) $ \MsgPong -> ReceiverDone ())
      sCollect
      sYield (ClientAgency TokIdle) MsgDone