{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE TypeOperators #-}

module Network.TypedProtocol.Core where

import           Data.Void (Void)
import Indexed.Functor

class Protocol ps where

  data Message ps (st :: ps) (st' :: ps)

  data ClientHasAgency (st :: ps)

  data ServerHasAgency (st :: ps)

  data NobodyHasAgency (st :: ps)

  exclusionLemma_ClientAndServerHaveAgency
    :: forall (st :: ps).
       ClientHasAgency st
    -> ServerHasAgency st
    -> Void

  exclusionLemma_NobodyAndClientHaveAgency
    :: forall (st :: ps).
       NobodyHasAgency st
    -> ClientHasAgency st
    -> Void

  exclusionLemma_NobodyAndServerHaveAgency
    :: forall (st :: ps).
       NobodyHasAgency st
    -> ServerHasAgency st
    -> Void

data PeerRole = AsClient | AsServer

data TokPeerRole (peerRole :: PeerRole) where
    TokAsClient :: TokPeerRole AsClient
    TokAsServer :: TokPeerRole AsServer

data PeerHasAgency (pr :: PeerRole) (st :: ps) where
  ClientAgency :: !(ClientHasAgency st) -> PeerHasAgency AsClient st
  ServerAgency :: !(ServerHasAgency st) -> PeerHasAgency AsServer st

instance ( forall (st' :: ps). Show (ClientHasAgency st')
         , forall (st' :: ps). Show (ServerHasAgency st')
         ) => Show (PeerHasAgency pr (st :: ps)) where
    show (ClientAgency stok) = "ClientAgency " ++ show stok
    show (ServerAgency stok) = "ServerAgency " ++ show stok

type WeHaveAgency   (pr :: PeerRole) st = PeerHasAgency             pr  st

type TheyHaveAgency (pr :: PeerRole) st = PeerHasAgency (FlipAgency pr) st

type family FlipAgency (pr :: PeerRole) where
  FlipAgency AsClient = AsServer
  FlipAgency AsServer = AsClient

data Peer ps (pr :: PeerRole) m q (st :: ps)  where

  PReturn ::  q st -> Peer ps pr m q st

  Done   :: !(NobodyHasAgency st)
         -> At a st st
         -> Peer ps pr m p st 

  Effect :: m (Peer ps pr m q st )
         ->    Peer ps pr m q st 

  Yield  :: !(WeHaveAgency pr st)
         -> Message ps st st'
         -> Peer ps pr m q st' 
         -> Peer ps pr m q st  

  Await  :: !(TheyHaveAgency pr st)
         -> (Message ps st ~> Peer ps pr m q )
         -> Peer ps pr m q st 

instance Functor m => IFunctor (Peer ps pr m) where
  imap f (PReturn q)   = PReturn (f q)
  imap _ (Done nha a) = Done nha a
  imap f (Effect mq)   = Effect (fmap (imap f) mq)
  imap f (Yield a b c) = Yield a b (imap f c)
  imap f (Await a f')  = Await a (imap f . f')

instance Functor m => IApplicative (Peer ps pr m) where
  ireturn = PReturn

instance Functor m => IMonad (Peer ps pr m) where
  ibind f (PReturn q)   = f q
  ibind _ (Done nha a)  = Done nha a
  ibind f (Effect mq)   = Effect (fmap (ibind f) mq)
  ibind f (Yield a b c) = Yield a b (ibind f c)
  ibind f (Await a f')  = Await a (ibind f . f')

yield :: WeHaveAgency pr st -> Message ps st st' -> Peer ps pr m (At () st') st
yield wha msg = Yield wha msg (PReturn $ At ())

await :: TheyHaveAgency pr st -> Peer ps pr m (Message ps st) st
await tha = Await tha PReturn

effect :: Functor m => m a -> Peer ps pr m (At a st) st
effect ma = Effect (fmap (PReturn . At) ma)

done :: NobodyHasAgency st -> a -> Peer ps pr m p st
done nha a = Done nha (At a) 

atReturn :: a -> Peer ps pr m (At a i) i 
atReturn a = PReturn (At a)