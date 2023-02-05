
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DeriveFunctor            #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}


module Network.Redesign.Peer where

import           Data.Kind (Type)
import           Data.Singletons

import           Network.Redesign.Core as Core


type Peer :: forall ps
          -> PeerRole
          -> IsPipelined
          -> Queue ps
          -> ps
          -> (Type -> Type)
          -- ^ monad's kind
          -> (Type -> Type)
          -- ^ stm monad's kind, usually @'STM' m@
          -> Type
          -> Type
data Peer ps pr pl q st m stm a where


  Effect
    :: forall ps pr pl q st m stm a.
       m (Peer ps pr pl q st m stm a)
    -- ^ monadic continuation
    ->    Peer ps pr pl q st m stm a


  Yield
    :: forall ps pr pl (st :: ps) (st' :: ps) m stm a.
       ( SingI st
       , SingI st'
       , ActiveState st
       )
    => WeHaveAgencyProof pr st
    -- ^ agency proof
    -> Message ps st st'
    -- ^ protocol message
    -> Peer ps pr pl Empty st' m stm a
    -- ^ continuation
    -> Peer ps pr pl Empty st  m stm a


  Await
    :: forall ps pr pl (st :: ps) m stm a.
       ( SingI st
       , ActiveState st
       )
    => TheyHaveAgencyProof pr st
    -- ^ agency proof
    -> (forall (st' :: ps). Message ps st st'
        -> Peer ps pr pl Empty st' m stm a)
    -- ^ continuation
    -> Peer     ps pr pl Empty st  m stm a


  Done
    :: forall ps pr pl (st :: ps) m stm a.
       ( SingI st
       , StateAgency st ~ NobodyAgency
       )
    => NobodyHasAgencyProof pr st
    -- ^ (no) agency proof
    -> a
    -- ^ returned value
    -> Peer ps pr pl Empty st m stm a


  YieldPipelined
    :: forall ps pr (st :: ps) (st' :: ps) q st'' m stm a.
       ( SingI st
       , SingI st'
       , ActiveState st
       )
    => WeHaveAgencyProof pr st
    -- ^ agency proof
    -> Message ps st st'
    -- ^ protocol message
    -> Peer ps pr Pipelined (q |> Tr st' st'') st'' m stm a
    -- ^ continuation
    -> Peer ps pr Pipelined  q                 st   m stm a


  Collect
    :: forall ps pr (st' :: ps) (st'' :: ps) q st m stm a.
       ( SingI st'
       , ActiveState st'
       )
    => TheyHaveAgencyProof pr st'
    -- ^ agency proof
    -> Maybe (Peer ps pr Pipelined (Tr st' st'' <| q) st m stm a)
    -- ^ continuation, executed if no message has arrived so far
    -> (forall (stNext :: ps). Message ps st' stNext
        -> Peer ps pr Pipelined (Tr stNext st'' <| q) st m stm a)
    -- ^ continuation
    -> Peer     ps pr Pipelined (Tr st'    st'' <| q) st m stm a


  CollectDone
    :: forall ps pr (st :: ps) q (st' :: ps) m stm a.
       Peer ps pr Pipelined              q  st' m stm a
    -- ^ continuation
    -> Peer ps pr Pipelined (Tr st st <| q) st' m stm a

  CollectSTM
    :: forall ps pr (st' :: ps) (st'' :: ps) q (st :: ps) m stm a.
       ( SingI st'
       , ActiveState st'
       )
    => TheyHaveAgencyProof pr st'
    -- ^ agency proof
    -> stm (Peer ps pr Pipelined (Tr st' st'' <| q) st m stm a)
    -- ^ continuation, which is executed if it wins the race with the next
    -- message.
    -> (forall stNext. Message ps st' stNext
        -> Peer ps pr Pipelined (Tr stNext st'' <| q) st m stm a)
    -- ^ continuation
    -> Peer     ps pr Pipelined (Tr st'    st'' <| q) st m stm a

deriving instance (Functor m, Functor stm) => Functor (Peer ps (pr :: PeerRole) pl q (st :: ps) m stm)
