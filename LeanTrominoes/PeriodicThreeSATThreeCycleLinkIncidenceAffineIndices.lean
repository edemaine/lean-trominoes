/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListMapIndices
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceIndices

/-! # Affine indices inside fixed cycle-link incidence blocks -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Link position `t` contributes its two local cycle incidences at `2t` and
`2t+1`. -/
theorem cycleLinkIncidences_zipIdx
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkIncidences source).zipIdx =
      ((allCycleLinks source).zipIdx source.clauses.length).zipIdx.flatMap
        fun taggedLink =>
          (cycleLinkIncidenceBlock taggedLink.1).zipIdx
            (2 * taggedLink.2) := by
  unfold cycleLinkIncidences
  simpa using
    (List.flatMap_zipIdx_fixed
      ((allCycleLinks source).zipIdx source.clauses.length)
      cycleLinkIncidenceBlock 2 0
      cycleLinkIncidenceBlock_length)

theorem cycleLinkSourceIncidence_tagged_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink :
      ((ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable) × Nat) × Nat)
    (taggedLinkMember : taggedLink ∈
      ((allCycleLinks source).zipIdx source.clauses.length).zipIdx) :
    (cycleLinkSourceIncidence taggedLink.1,
        2 * taggedLink.2) ∈
      (cycleLinkIncidences source).zipIdx := by
  rw [cycleLinkIncidences_zipIdx]
  apply List.mem_flatMap.mpr
  refine ⟨taggedLink, taggedLinkMember, ?_⟩
  simp [cycleLinkIncidenceBlock]

theorem cycleLinkTargetIncidence_tagged_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink :
      ((ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable) × Nat) × Nat)
    (taggedLinkMember : taggedLink ∈
      ((allCycleLinks source).zipIdx source.clauses.length).zipIdx) :
    (cycleLinkTargetIncidence taggedLink.1,
        2 * taggedLink.2 + 1) ∈
      (cycleLinkIncidences source).zipIdx := by
  rw [cycleLinkIncidences_zipIdx]
  apply List.mem_flatMap.mpr
  refine ⟨taggedLink, taggedLinkMember, ?_⟩
  simp [cycleLinkIncidenceBlock]

/-- Link position `t` has full-formula negative-source edge index `n+2t`. -/
theorem cycleLinkSourceIncidence_tagged_mem_formula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink :
      ((ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable) × Nat) × Nat)
    (taggedLinkMember : taggedLink ∈
      ((allCycleLinks source).zipIdx source.clauses.length).zipIdx) :
    (cycleLinkSourceIncidence taggedLink.1,
        PeriodicCNF.presentationLiteralCount source +
          2 * taggedLink.2) ∈
      (PeriodicCNF.incidencesWithMetadata (formula source)).zipIdx := by
  exact cycleLinkIncidence_tagged_mem_formula source
    (cycleLinkSourceIncidence taggedLink.1, 2 * taggedLink.2)
    (cycleLinkSourceIncidence_tagged_mem
      source taggedLink taggedLinkMember)

/-- Link position `t` has full-formula positive-target edge index `n+2t+1`. -/
theorem cycleLinkTargetIncidence_tagged_mem_formula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink :
      ((ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable) × Nat) × Nat)
    (taggedLinkMember : taggedLink ∈
      ((allCycleLinks source).zipIdx source.clauses.length).zipIdx) :
    (cycleLinkTargetIncidence taggedLink.1,
        PeriodicCNF.presentationLiteralCount source +
          (2 * taggedLink.2 + 1)) ∈
      (PeriodicCNF.incidencesWithMetadata (formula source)).zipIdx := by
  exact cycleLinkIncidence_tagged_mem_formula source
    (cycleLinkTargetIncidence taggedLink.1, 2 * taggedLink.2 + 1)
    (cycleLinkTargetIncidence_tagged_mem
      source taggedLink taggedLinkMember)

end PeriodicThreeSATThree
end LeanTrominoes
