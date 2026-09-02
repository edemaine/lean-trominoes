/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFlatMapAligned
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceElementCodeSemantics

/-! # Baseline clause-core incidence multiplicities -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicCNF PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- Three internal references and two references to each terminal, for each
of the three canonical colors. -/
def finalClauseCoreExpectedElementTagBlock : List Nat :=
  [16, 16, 16, 17, 17, 18, 18, 19, 19,
    20, 20, 20, 21, 21, 22, 22, 23, 23,
    24, 24, 24, 25, 25, 26, 26, 27, 27]

/-- The finite nine-triple clause table has its claimed baseline
multiplicities. -/
theorem finalClauseIncidenceElementTagBlock_perm_expected
    (fan : ClauseRibbonFanData) :
    (finalClauseIncidenceElementTagBlock fan).Perm
      finalClauseCoreExpectedElementTagBlock := by
  unfold finalClauseIncidenceElementTagBlock
    finalClauseCoreExpectedElementTagBlock allClauseSets
    clauseIncidenceReferenceTag clauseIncidenceElementTag
    X3CClauseSet.coloredReferences
    directSourceFinalClauseElementColorTagBase
  native_decide

/-- The exact compiled code block belonging to one actual clause position. -/
def finalClauseIncidenceElementCodeBlock
    (index : Nat) (fan : ClauseRibbonFanData) : List Nat :=
  List.zipWith (fun base tag => base + tag)
    (List.replicate 27 (index * directSourceFinalElementCodeStride))
    (finalClauseIncidenceElementTagBlock fan)

/-- The baseline multiplicity block under one stride-scaled clause index. -/
def finalClauseCoreExpectedElementCodeBlock (index : Nat) : List Nat :=
  finalClauseCoreExpectedElementTagBlock.map fun tag =>
    index * directSourceFinalElementCodeStride + tag

theorem finalClauseIncidenceElementCodeBlock_eq_map
    (index : Nat) (fan : ClauseRibbonFanData) :
    finalClauseIncidenceElementCodeBlock index fan =
      (finalClauseIncidenceElementTagBlock fan).map fun tag =>
        index * directSourceFinalElementCodeStride + tag := by
  unfold finalClauseIncidenceElementCodeBlock
  rw [show 27 = (finalClauseIncidenceElementTagBlock fan).length by
    exact (finalClauseIncidenceElementTagBlock_length fan).symm]
  exact List.zipWith_replicate_left (fun base tag => base + tag)
    (index * directSourceFinalElementCodeStride)
    (finalClauseIncidenceElementTagBlock fan)

/-- Lifting the finite tag audit through the common clause base gives the
baseline code multiplicities at every descriptor. -/
theorem finalClauseIncidenceElementCodeBlock_perm_expected
    (index : Nat) (fan : ClauseRibbonFanData) :
    (finalClauseIncidenceElementCodeBlock index fan).Perm
      (finalClauseCoreExpectedElementCodeBlock index) := by
  rw [finalClauseIncidenceElementCodeBlock_eq_map]
  unfold finalClauseCoreExpectedElementCodeBlock
  exact (finalClauseIncidenceElementTagBlock_perm_expected fan).map _

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The arithmetic compiler is a flattening of one explicit 27-reference
block per actual final-clause position. -/
theorem directSourceFinalClauseIncidenceElementCodes_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalClauseIncidenceElementCodes decider symbols =
      (List.zipWith finalClauseIncidenceElementCodeBlock
        (List.range
          (directSourceFinalClauseFans decider symbols).length)
        (directSourceFinalClauseFans decider symbols)).flatten := by
  rw [directSourceFinalClauseIncidenceElementCodes_eq_zipWith,
    directSourceFinalClauseIncidenceIndices_eq_range,
    directSourceFinalClauseIncidenceElementTags_eq_flatMap]
  unfold directSourceFinalClauseIncidenceElementCodeBases
    UnaryFieldFixedCopies.values UnaryFieldConstantScale.values
  rw [List.flatMap_map]
  rw [List.zipWith_flatMap_aligned
    (fun base tag => base + tag)
    (fun index =>
      List.replicate 27
        (index * directSourceFinalElementCodeStride))
    finalClauseIncidenceElementTagBlock
    (fun _ token => by simp)]
  rfl

/-- Globally, clause-core incidences contribute the baseline three/two
multiplicity block at every canonical clause position. -/
theorem directSourceFinalClauseIncidenceElementCodes_perm_expected
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncidenceElementCodes decider symbols).Perm
      ((List.range
        (directSourceFinalClauseFans decider symbols).length).flatMap
          finalClauseCoreExpectedElementCodeBlock) := by
  rw [directSourceFinalClauseIncidenceElementCodes_eq_blocks]
  exact List.zipWith_flatten_perm_flatMap_left_of_length_eq
    finalClauseIncidenceElementCodeBlock
    finalClauseCoreExpectedElementCodeBlock
    finalClauseIncidenceElementCodeBlock_perm_expected
    (List.range
      (directSourceFinalClauseFans decider symbols).length)
    (directSourceFinalClauseFans decider symbols) (by simp)

end LeanTrominoes.PeriodicCNFStripReduction

end
