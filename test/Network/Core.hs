{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
module Network.Core where

import Network.TypedProtocol.Core
import Indexed.Functor as I
import Control.Effect.State (State, get, modify)
import Control.Algebra (Has)
import Control.Effect.Lift (Lift)
import Control.Carrier.Lift (sendIO)

-- example PingPong
------------------------------------------------------------------------------
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


pingPongClientPeer :: Has (State Int) sig m 
                   => Peer PingPong AsClient m (At () StDone) StIdle
pingPongClientPeer = I.do
    -- ghc bug: https://gitlab.haskell.org/ghc/ghc/-/issues/22788 
    -- we can't use this: 
    --
    -- i <- effect (get @Int) 
    -- if i > 10 
    --   then  ...
    --   else ...
    effect (get @Int) I.>>= 
      \(At i ) ->
         if i > 10 
          then I.do
            yield (ClientAgency TokIdle) MsgDone
            preturn ()
          else I.do
            yield (ClientAgency TokIdle) MsgPing 
            effect $ modify @Int (+1)
            await (ServerAgency TokBusy) I.>>= \case
              MsgPong -> pingPongClientPeer

pingPongServerPeer :: Has (Lift IO ) sig m 
                   => Peer PingPong AsServer m (At () StDone) StIdle
pingPongServerPeer = Indexed.do 
    await (ClientAgency TokIdle) I.>>= \case
      MsgDone -> I.do 
        effect $ sendIO (print "recv MsgDone, finish")
        preturn ()
      MsgPing -> I.do 
        effect $ sendIO (print "recv MsgPing, send MsgPong")
        yield (ServerAgency TokBusy) MsgPong
        pingPongServerPeer
------------------------------------------------------------------------------