/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OccurrenceSplitRingOccurrenceOrder
import LeanTrominoes.PeriodicEightOccurrenceSplitDegreeThreeOriginal

/-!
# Indexing semantic implication-cycle occurrences

The finite Figure 7 cycle certificate uses local clause/literal indices,
whereas the semantic occurrence-splitting formula uses renamed periodic
literals.  This file proves that renaming preserves the complete flattened
incidence presentation.  Consequently, filtering one semantic ring to a
particular real copy yields exactly the two local indices certified in
`OccurrenceSplitRingOccurrenceOrder`.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree
open PlanarThreeSAT

/-- Rename one local embedded incidence and shift its clause index to an
arbitrary surrounding presentation. -/
def periodicCycleOccurrence
    {Variable : Type*}
    (start : Nat) (atom : Variable)
    (incidence : EmbeddedCNFIncidence RingVertex) :
    PeriodicOneInThreeToThreeDM.TaggedOccurrence
      (ThreeOccurrenceVariable Variable) :=
  (⟨ringCopy atom incidence.literal.1,
      (0, 0), incidence.literal.2⟩,
    start + incidence.clauseIndex,
    incidence.literalIndex)

/-- A renamed semantic implication cycle has exactly the zero-based local
embedded incidences, with only atoms changed. -/
theorem taggedLiteralsFrom_cycleClausesFor
    {Variable : Type*}
    (atom : Variable) :
    taggedLiteralsFrom 0 (cycleClausesFor atom) =
      (embeddedCNFIncidences cycleFormula).map
        (periodicCycleOccurrence 0 atom) := by
  rw [OccurrenceSplitRing.cycleClausesFor_eq_cycleFormula]
  unfold taggedLiteralsFrom embeddedCNFIncidences
  rw [List.zipIdx_map]
  simp only [List.flatMap_map]
  rw [List.map_flatMap]
  congr 1
  funext taggedClause
  rcases taggedClause with ⟨clause, clauseIndex⟩
  simp only [Prod.map, id_eq]
  unfold periodicCycleClause
  rw [List.zipIdx_map]
  simp only [List.map_map, Function.comp_def]
  simp [periodicCycleOccurrence, Prod.map]

/-- Local clause/literal indices of one copy within its semantic
implication ring. -/
def cycleOccurrenceIndicesFor
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable)
    (output : ThreeOccurrenceVariable Variable) :
    List (Nat × Nat) :=
  (taggedLiteralsFrom 0 (cycleClausesFor atom))
    |>.filter (fun tagged => tagged.1.atom = output)
    |>.map fun tagged => (tagged.2.1, tagged.2.2)

/-- Filtering a renamed semantic ring to one local vertex preserves exactly
that vertex's local occurrence-index list. -/
theorem cycleOccurrenceIndicesFor_ringCopy
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (vertex : RingVertex) :
    cycleOccurrenceIndicesFor atom (ringCopy atom vertex) =
      cycleOccurrenceIndicesAt vertex := by
  unfold cycleOccurrenceIndicesFor cycleOccurrenceIndicesAt
  rw [taggedLiteralsFrom_cycleClausesFor]
  generalize
    embeddedCNFIncidences cycleFormula = incidences
  induction incidences with
  | nil =>
      rfl
  | cons incidence rest induction =>
      by_cases same : incidence.literal.1 = vertex
      · simp [same, induction,
          periodicCycleOccurrence]
      · have renamedDifferent :
            ringCopy atom incidence.literal.1 ≠
              ringCopy atom vertex := by
          intro equal
          exact same (ringCopy_injective atom equal)
        simp [same, renamedDifferent, induction,
          periodicCycleOccurrence]

/-- At every real port, the semantic implication ring contributes exactly
two occurrences in the same local order used by the geometric certificate. -/
@[simp]
theorem cycleOccurrenceIndicesFor_copy_length
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (port : Port) :
    (cycleOccurrenceIndicesFor atom (copy atom port)).length = 2 := by
  rw [show copy atom port = ringCopy atom (.port port) by rfl,
    cycleOccurrenceIndicesFor_ringCopy,
    cycleOccurrenceIndicesAt_port_length]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
