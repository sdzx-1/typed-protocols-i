{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DeriveFunctor            #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies   #-}
{-# LANGUAGE TypeInType               #-}
-- need for 'Show' instance of 'ProtocolState'
{-# LANGUAGE UndecidableInstances     #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}


-- | This module defines the core of the typed protocol framework.
--

module Network.Redesign.Core
  ( -- * Introduction
    -- $intro
    -- * Defining protocols
    -- $defining
    Protocol (..)
    -- $lemmas
    -- * Engaging in protocols
  , PeerRole (..)
  , SingPeerRole (..)
  , Agency (..)
  , SingAgency (..)
  , RelativeAgency (..)
  , Relative
  , ReflRelativeAgency (..)
  , WeHaveAgencyProof
  , TheyHaveAgencyProof
  , NobodyHasAgencyProof
  , FlipAgency
  , IsPipelined (..)
  , Transition (..)
  , SingTrans (..)
  , Queue (..)
  , type (<|)
  , type (|>)
  , SingQueueF (..)
  , (|>)
  , ActiveAgency
  , ActiveAgency' (..)
  , IsActiveState (..)
  , ActiveState
  , notActiveState
    -- * Utils
  , stateToken
  ) where

import           Data.Kind (Constraint, Type)
import           Data.Type.Queue

import           Data.Singletons


data PeerRole = AsClient | AsServer

type SingPeerRole :: PeerRole -> Type
data SingPeerRole pr where
    SingAsClient :: SingPeerRole AsClient
    SingAsServer :: SingPeerRole AsServer

deriving instance Show (SingPeerRole pr)

type instance Sing = SingPeerRole
instance SingI AsClient where
    sing = SingAsClient
instance SingI AsServer where
    sing = SingAsServer


data Agency where
    -- | The client has agency.
    ClientAgency :: Agency

    -- | The server has agency.
    ServerAgency :: Agency

    -- | Nobody has agency, terminal state.
    NobodyAgency :: Agency

type SingAgency :: Agency -> Type
data SingAgency a where
    SingClientAgency :: SingAgency ClientAgency
    SingServerAgency :: SingAgency ServerAgency
    SingNobodyAgency :: SingAgency NobodyAgency

deriving instance Show (SingAgency a)

type instance Sing = SingAgency
instance SingI ClientAgency where
    sing = SingClientAgency
instance SingI ServerAgency where
    sing = SingServerAgency
instance SingI NobodyAgency where
    sing = SingNobodyAgency

-- | A promoted data type which indicates the effective agency (which is
-- relative to current role).
--
data RelativeAgency where
    WeHaveAgency    :: RelativeAgency
    TheyHaveAgency  :: RelativeAgency
    NobodyHasAgency :: RelativeAgency


-- | Compute effective agency with respect to the peer role, for client role,
-- agency is preserved, while for the server role it is flipped.
--
type        Relative :: PeerRole -> Agency -> RelativeAgency
type family Relative  pr a where
  Relative AsClient ClientAgency = WeHaveAgency
  Relative AsClient ServerAgency = TheyHaveAgency
  Relative AsClient NobodyAgency = NobodyHasAgency
  Relative AsServer ClientAgency = TheyHaveAgency
  Relative AsServer ServerAgency = WeHaveAgency
  Relative AsServer NobodyAgency = NobodyHasAgency


-- | Type equality for 'RelativeAgency' which also carries information about
-- agency.  It is isomorphic to a product of 'Agency' singleton and
-- @r :~: r'@, where both @r@ and @r'@ have kind 'RelativeAgency'.
--
type ReflRelativeAgency :: Agency -> RelativeAgency -> RelativeAgency -> Type
data ReflRelativeAgency a r r' where
    ReflClientAgency :: ReflRelativeAgency ClientAgency r r
    ReflServerAgency :: ReflRelativeAgency ServerAgency r r
    ReflNobodyAgency :: ReflRelativeAgency NobodyAgency r r

-- | Type of the proof that we have the agency.
--
-- 'ReflClientAgency' has this type only iff `'StateAgency' st ~ 'ClientAgency'`
-- and `pr ~ 'AsClient'`.
--
-- 'ReflServerAgency' has this type only iff `'StateAgency' st ~ 'ServerAgency'`
-- and `pr ~ 'AsServer'`
--
type WeHaveAgencyProof :: PeerRole -> ps -> Type
type WeHaveAgencyProof pr st = ReflRelativeAgency
                                 (StateAgency st)
                                  WeHaveAgency
                                 (Relative pr (StateAgency st))

-- | Type of the proof that the remote side has the agency.
--
-- 'ReflClientAgency' has this type only iff `'StateAgency' st ~ 'ClientAgency'`
-- and `pr ~ 'AsServer'`.
--
-- 'ReflServerAgency' has this type only iff `'StateAgency' st ~ 'ServerAgency'`
-- and `pr ~ 'AsClient'`
--
type TheyHaveAgencyProof :: PeerRole -> ps -> Type
type TheyHaveAgencyProof pr st = ReflRelativeAgency
                                   (StateAgency st)
                                    TheyHaveAgency
                                   (Relative pr (StateAgency st))


-- | Type of the proof that nobody has agency in this state.
--
-- Only 'ReflNobodyAgency' can fulfil the proof obligation.
--
type NobodyHasAgencyProof :: PeerRole -> ps -> Type
type NobodyHasAgencyProof pr st = ReflRelativeAgency (StateAgency st)
                                                      NobodyHasAgency
                                                     (Relative pr (StateAgency st))

class Protocol ps where

  -- | The messages for this protocol. It is expected to be a GADT that is
  -- indexed by the @from@ and @to@ protocol states. That is the protocol state
  -- the message transitions from, and the protocol state it transitions into.
  -- These are the edges of the protocol state transition system.
  --
  data Message ps (st :: ps) (st' :: ps)

  -- | Associate an 'Agency' for each state.
  --
  type StateAgency (st :: ps) :: Agency

  -- | A type alias for protocol state token, e.g. term level representation of
  -- type level state (also known as singleton).
  --
  type StateToken :: ps -> Type

-- | An alias for 'sing'.
--
stateToken :: (SingI st, Sing st ~ StateToken st) => StateToken st
stateToken = sing

type ActiveAgency' :: ps -> Agency -> Type
data ActiveAgency' st agency where
  ClientHasAgency :: StateAgency st ~ ClientAgency
                  => ActiveAgency' st ClientAgency
  ServerHasAgency :: StateAgency st ~ ServerAgency
                  => ActiveAgency' st ServerAgency

deriving instance Show (ActiveAgency' st agency)

type ActiveAgency :: ps -> Type
type ActiveAgency st = ActiveAgency' st (StateAgency st)

-- | A type class which restricts states to ones that have `ClientAgency` or
-- `ServerAgency`, excluding `NobodyAgency`.
--
-- One can use `notActive' to eliminate cases for which both @'IsActiveState'
-- st@ is in scope and for which we have an evidence that the state is not
-- active (i.e. a singleton).  This is useful when writing a 'Codec'.
--
class IsActiveState st (agency :: Agency) where
  activeAgency :: ActiveAgency' st agency

instance ClientAgency ~ StateAgency st
      => IsActiveState st ClientAgency where
  activeAgency = ClientHasAgency
instance ServerAgency ~ StateAgency st
      => IsActiveState st ServerAgency where
  activeAgency = ServerHasAgency

type ActiveState :: ps -> Constraint
type ActiveState st = IsActiveState st (StateAgency st)

notActiveState :: forall ps (st :: ps).
                  StateAgency st ~ NobodyAgency
               => ActiveState st
               => Sing st
               -> forall a. a
notActiveState (_ :: Sing st) =
  case activeAgency :: ActiveAgency st of {}


-- | A type function to flip the client and server roles.
--
type        FlipAgency :: PeerRole -> PeerRole
type family FlipAgency pr where
  FlipAgency AsClient = AsServer
  FlipAgency AsServer = AsClient

-- | Promoted data type which indicates if 'Peer' is used in
-- pipelined mode or not.
--
data IsPipelined = NonPipelined | Pipelined
