
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


module Network.Redesign.T where

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
          -> Type
          -> Type
data Peer ps pr pl q st m a where


  Effect
    :: forall ps pr pl q st m a.
       m (Peer ps pr pl q st m a)
    -- ^ monadic continuation
    ->    Peer ps pr pl q st m a


  Yield
    :: forall ps pr pl (st :: ps) (st' :: ps) m a.
       ( SingI st
       , SingI st'
       , ActiveState st
       )
    => WeHaveAgencyProof pr st
    -- ^ agency proof
    -> Message ps st st'
    -- ^ protocol message
    -> Peer ps pr pl Empty st' m a
    -- ^ continuation
    -> Peer ps pr pl Empty st  m a


  Await
    :: forall ps pr pl (st :: ps) m a.
       ( SingI st
       , ActiveState st
       )
    => TheyHaveAgencyProof pr st
    -- ^ agency proof
    -> (forall (st' :: ps). Message ps st st'
        -> Peer ps pr pl Empty st' m a)
    -- ^ continuation
    -> Peer     ps pr pl Empty st  m a


  Done
    :: forall ps pr pl (st :: ps) m a.
       ( SingI st
       , StateAgency st ~ NobodyAgency
       )
    => NobodyHasAgencyProof pr st
    -- ^ (no) agency proof
    -> a
    -- ^ returned value
    -> Peer ps pr pl Empty st m a


  YieldPipelined
    :: forall ps pr (st :: ps) (st' :: ps) q st'' m a.
       ( SingI st
       , SingI st'
       , ActiveState st
       )
    => WeHaveAgencyProof pr st
    -- ^ agency proof
    -> Message ps st st'
    -- ^ protocol message
    -> Peer ps pr Pipelined (q |> Tr st' st'') st'' m a
    -- ^ continuation
    -> Peer ps pr Pipelined  q                 st   m a


  Collect
    :: forall ps pr (st' :: ps) (st'' :: ps) q st m a.
       ( SingI st'
       , ActiveState st'
       )
    => TheyHaveAgencyProof pr st'
    -- ^ agency proof
    -> (forall (stNext :: ps). Message ps st' stNext
        -> Peer ps pr Pipelined (Tr stNext st'' <| q) st m a)
    -- ^ continuation
    -> Peer     ps pr Pipelined (Tr st'    st'' <| q) st m a


  CollectDone
    :: forall ps pr (st :: ps) q (st' :: ps) m a.
       Peer ps pr Pipelined              q  st' m a
    -- ^ continuation
    -> Peer ps pr Pipelined (Tr st st <| q) st' m a


deriving instance (Functor m) => Functor (Peer ps (pr :: PeerRole) pl q (st :: ps) m)
