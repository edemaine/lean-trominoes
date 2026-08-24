/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCrossingRecordData

/-! # Retained carrier nodes reconstructed from occurrence pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The two terminal carrier nodes of one segment occurrence. -/
def occurrenceCarrierTerminalNodes
    (occurrence : IndexedGridSegment × Cell) : List CarrierNode :=
  (occurrenceTerminals occurrence).map CarrierNode.terminal

/-- The four boundary carrier nodes of one physical crossing record. -/
def crossingRecordCarrierBoundaryNodes
    (record : CrossingRecord) : List CarrierNode :=
  ([⟨record, .left⟩, ⟨record, .right⟩,
      ⟨record, .top⟩, ⟨record, .bottom⟩] :
    List CrossingBoundary).map CarrierNode.boundary

/-- Exact retained carrier-node stream reconstructed from arbitrary ordered
neighbor occurrences and accepted crossing pairs. -/
def retainedCarrierNodesOfOccurrencesAndPairsAtPeriod
    (period : Nat)
    (occurrences : List (IndexedGridSegment × Cell))
    (pairs : List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))) : List CarrierNode :=
  occurrences.flatMap occurrenceCarrierTerminalNodes ++
    (occurrencePairRetainedCrossingRecordScanAtPeriod period pairs).flatMap
      crossingRecordCarrierBoundaryNodes

end LeanTrominoes.PeriodicOrthocrossing
