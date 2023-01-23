{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Network.TypedProtocol.T where

import Network.TypedProtocol.Pipelined
import Network.TypedProtocol.Core
import Data.Kind (Type)
import Indexed.Functor
import Indexed.Functor as I


data K ps ::  (n, st) -> (n, st) -> Type where
    K :: Message ps st st' -> K ps '(n, st) '(n, st')

data PS ps pr c m q (k :: (N, st)) where

    SReturn :: q k -> PS ps pr c m q k

    SEffect :: m (PS ps pr c m q k) -> PS ps pr c m q k

    SYield :: (WeHaveAgency pr st) 
           -> K ps '(any, st) '(any, st')
           -> PS ps pr c m q '(Z, st')
           -> PS ps pr c m q '(Z, st)

    SAwait :: TheyHaveAgency pr st 
           -> (K ps '(any, st) ~> PS ps pr c m q )
           -> PS ps pr c m q '(Z, st)

    SPipeline :: WeHaveAgency pr st  
              -> K ps '(any, st) '(any, st')
              -> PeerReceiver ps pr st' st'' m c 
              -> PS ps pr  c m q '(S n , st'')
              -> PS ps pr c m q '(n, st)

    -- SCollect :: Maybe (PS ps pr c m q '(S n, st))
    --               -> (c -> PS ps pr c m q '(n, st))
    --               -> PS ps pr c m q '(S n , st)

instance Functor m => IFunctor (PS ps pr c m)  where
    imap f (SReturn q) = SReturn (f q)
    imap f (SEffect mq) = SEffect (fmap (imap f) mq)
    imap f (SYield wha msg ps) = SYield wha msg (imap f ps)
    imap f (SAwait tha cont) = SAwait tha (imap f . cont)
    imap f (SPipeline wha msg pRecv ps) = SPipeline wha msg pRecv (imap f ps)
    -- imap f (SCollect mbp cont ) = SCollect (fmap (imap f) mbp) (imap f . cont)

instance Functor m => IApplicative (PS ps pr c m) where
    ireturn = SReturn

instance Functor m => IMonad (PS ps pr c m) where
    ibind f (SReturn q) = f q
    ibind f (SEffect mq) = SEffect (fmap (ibind f) mq)
    ibind f (SYield wha msg ps) = SYield wha msg (ibind f ps)
    ibind f (SAwait tha cont) = SAwait tha (ibind f . cont)
    ibind f (SPipeline wha msg pRecv ps) = SPipeline wha msg pRecv (ibind f ps)
    -- ibind f (SCollect mbp cont ) = SCollect (fmap (ibind f) mbp) (ibind f . cont)


sReturn :: a -> PS ps pr c m (At a i) i
sReturn a = SReturn (At a)

effect :: Functor m => m a -> PS ps pr c m (At a st) st
effect ma = SEffect (fmap (SReturn . At ) ma)

sYield :: WeHaveAgency pr st 
       -> K ps  '(Z, st) '(Z, st')
       -> PS ps pr c m (At () '(Z,st')) '(Z, st)
sYield wha msg = SYield wha msg (SReturn (At ()))

sAwait :: TheyHaveAgency pr st 
       -> PS ps pr c m (K ps '(Z, st)) '(Z, st)
sAwait tha =  SAwait tha SReturn 

sPipeline :: WeHaveAgency pr st  
          -> K ps '(any, st) '(any, st')
          -> PeerReceiver ps pr st' st'' m c 
          -> PS ps pr c m (At () '(S n , st'')) '(n, st)
sPipeline wha msg precv  = 
    SPipeline wha msg precv (SReturn (At ()))


    -- SCollect :: Maybe (PS ps pr c m q '(S n, st))
    --               -> (c -> PS ps pr c m q '(n, st))
    --               -> PS ps pr c m q '(S n , st)

----------------- example -----------------
-------------------------------------------


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


ppClientPeerSender :: Functor m 
                   => PS PingPong AsClient c m (At () '(Z, StDone)) '(Z, StIdle)
ppClientPeerSender = I.do
    sYield (ClientAgency TokIdle) (K MsgPing)
    K v <- sAwait (ServerAgency TokBusy)
    case v of 
        MsgPong -> 
            sYield (ClientAgency TokIdle) (K MsgDone)


ppSender :: Functor m 
         => PS PingPong AsClient c m (At () '(Z, StDone)) '(Z, StIdle)
ppSender = I.do 
    sPipeline (ClientAgency TokIdle) (K MsgPing) (ReceiverAwait (ServerAgency TokBusy) $ \MsgPong -> undefined)
    sPipeline (ClientAgency TokIdle) (K MsgPing) (ReceiverAwait (ServerAgency TokBusy) $ \MsgPong -> undefined)
    sPipeline (ClientAgency TokIdle) (K MsgPing) (ReceiverAwait (ServerAgency TokBusy) $ \MsgPong -> undefined)
    sPipeline (ClientAgency TokIdle) (K MsgPing) (ReceiverAwait (ServerAgency TokBusy) $ \MsgPong -> undefined)
    undefined