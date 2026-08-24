/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierKeyCandidateData

/-! # Crossing-major retained carrier-key scan -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The four carrier-key occurrences contributed by one retained translate
of a canonical horizontal-first crossing. -/
def retainedCrossingCarrierKeyShiftBlock
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (crossing : CrossingRecord)
    (shift : Cell) : List (Nat × Nat × Cell) :=
  let translated := crossing.periodTranslate graph shift
  let horizontal := occurrenceCarrierKey
    (translated.first, translated.firstTranslate)
  let vertical := occurrenceCarrierKey
    (translated.second, translated.secondTranslate)
  [horizontal, horizontal, vertical, vertical]

/-- All retained shift blocks of one canonical crossing. -/
def retainedCrossingCarrierKeyBlock
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (crossing : CrossingRecord) :
    List (Nat × Nat × Cell) :=
  carrierCrossingRetentionShifts.flatMap
    (retainedCrossingCarrierKeyShiftBlock graph crossing)

/-- Exact crossing-major candidate scan for retained boundary carrier keys. -/
def retainedCrossingCarrierKeyScan
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  (orientedCrossings graph).flatMap
    (retainedCrossingCarrierKeyBlock graph)

end LeanTrominoes.PeriodicOrthocrossing
