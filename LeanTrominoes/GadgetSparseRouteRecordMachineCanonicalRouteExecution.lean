/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCanonicalMetadataExecution
import LeanTrominoes.GadgetSparseRouteRecordMachineRouteExecution

/-! # Canonical request execution through the route loop -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.RouteRasterRequest

/-- Machine data after a canonical request has emitted all route records. -/
def canonicalAfterRouteData (request : Request) : TapeData :=
  locationData []
    (advanceDirections request.metadata.complementLocation
      (requestDirections request))
    (complementRecordBlock request).reverse []

/-- Exact allowance through metadata parsing and route-record emission. -/
def canonicalRouteTime (request : Request) : Nat :=
  metadataTime request +
    routeTime request.metadata.complementLocation
      (requestDirections request)

/-- A valid canonical normalized block reaches reversal with exactly the
semantic complement-record word accumulated in reverse. -/
def canonicalRoute_evalsInTime (request : Request)
    (valid : request.metadata.CursorValid) :
    EvalsToInTime (TM2.step program)
      (initialCfg
        (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
          request))
      (some (cfg .reverseOutput (inputState .routeEnd)
        (canonicalAfterRouteData request)))
      (canonicalRouteTime request) := by
  have metadataRun := canonicalMetadata_evalsInTime request valid
  have routeRun := route_evalsInTime request.metadata.color
    (inputState (.color request.metadata.color))
    request.metadata.complementLocation (requestDirections request)
    [.routeEnd] [] [] (by simp [StopsDirections, inputState,
      isDirectionState])
  have whole := EvalsToInTime.trans (TM2.step program)
    (metadataTime request)
    (routeTime request.metadata.complementLocation
      (requestDirections request))
    (initialCfg
      (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
        request))
    (cfg (.scanIncoming request.metadata.color)
      (inputState (.color request.metadata.color))
      (locationData
        (directionInput (requestDirections request) [.routeEnd])
        request.metadata.complementLocation [] []))
    (some (cfg .reverseOutput (inputState .routeEnd)
      (canonicalAfterRouteData request)))
    (by simpa [initialCfg] using metadataRun)
    (by simpa [canonicalAfterRouteData, complementRecordBlock,
        requestDirections, stopState, stopTail] using routeRun)
  simpa [canonicalRouteTime, Nat.add_comm] using whole

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
