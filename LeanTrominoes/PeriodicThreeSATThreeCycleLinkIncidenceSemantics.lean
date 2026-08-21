/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleIncidenceSemantics
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceData
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkSemantics

/-! # Correctness of fixed occurrence-cycle incidence blocks -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Expanding all directed links into fixed two-incidence blocks recovers the
exact shifted cycle metadata suffix. -/
theorem cycleLinkIncidences_eq_cycleIncidences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    cycleLinkIncidences source = cycleIncidences source := by
  unfold cycleLinkIncidences cycleIncidences
  unfold PeriodicCNF.incidenceMetadataBlocksFrom
  rw [allCycleClauses_eq_map_allCycleLinks, List.zipIdx_map]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedLink taggedLinkMember
  cases taggedLink with
  | mk link clauseIndex =>
      cases link with
      | mk first second =>
          simp [cycleLinkIncidenceBlock,
            cycleLinkSourceIncidence, cycleLinkTargetIncidence,
            PeriodicCNF.incidenceMetadataBlock, implicationClause]

/-- The explicit link-incidence stream has exactly two records per source
literal occurrence. -/
@[simp] theorem cycleLinkIncidences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkIncidences source).length =
      2 * PeriodicCNF.presentationLiteralCount source := by
  rw [cycleLinkIncidences_eq_cycleIncidences]
  exact cycleIncidences_length source

end PeriodicThreeSATThree
end LeanTrominoes
