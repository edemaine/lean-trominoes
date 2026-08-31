/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendOccurrenceSlotBlockFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendTaggedClauseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierEqualityData
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance
import LeanTrominoes.RetainedAngularFanFinalBendRecordFamilyPresentation

/-! # Tagged-bend presentation of direct semantic slot blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendSemanticSlotPresentationStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalOriginalBaseDecidableEq
attribute [local instance]
  directSourceFinalOriginalBaseDecidableEq

local instance directFinalBendSemanticSlotPresentationVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalOriginalVariableDecidableEq

def directSourceFinalBendIndexedTaggedBends
    (symbols : List encoding.Γ) :
    List ((RouteBend × Bool) × Nat) :=
  ((baseRouteBends
    (directSourceFinalNormalizedFormula decider symbols)).product
      [true, false]).zipIdx
        (directSourceFinalBendStart decider symbols)

/-- Mixed-equality normal form obtained immediately after replacing the
direct bend clauses by their tagged-bend presentation. -/
private def directSourceFinalBendMixedSemanticOccurrenceSlotBlocks
    (symbols : List encoding.Γ) : List (List RetainedTerminalSlot) :=
  finalBendSemanticOccurrenceSlotBlocksAt
    directSourceFinalOriginalVariableDecidableEq
    directSourceVariableDecidableEq
    (directSourceFinalNormalizedFormula decider symbols)
    (directSourceFinalBendIndexedTaggedBends decider symbols)

/-- Named two-slot blocks for every indexed direct final bend implication. -/
def directSourceFinalBendTaggedSemanticOccurrenceSlotBlocks
    (symbols : List encoding.Γ) : List (List RetainedTerminalSlot) :=
  finalBendNamedSemanticOccurrenceSlotBlocksAt
    directSourceFinalOriginalVariableDecidableEq
    (directSourceFinalNormalizedFormula decider symbols)
    (directSourceFinalBendIndexedTaggedBends decider symbols)

private theorem directSourceFinalBendSemanticOccurrenceSlotBlocks_eq_mixed
    (symbols : List encoding.Γ) :
    directSourceFinalBendSemanticOccurrenceSlotBlocks decider symbols =
      directSourceFinalBendMixedSemanticOccurrenceSlotBlocks
        decider symbols := by
  unfold directSourceFinalBendSemanticOccurrenceSlotBlocks
    directSourceFinalBendMixedSemanticOccurrenceSlotBlocks
    directSourceFinalBendIndexedTaggedBends
    finalBendSemanticOccurrenceSlotBlocksAt
  rw [directSourceFormula_eq_finalNormalized]
  rw [directSourceFinalBendTaggedClauses_eq]
  rfl

private theorem directSourceFinalBendMixedSemanticOccurrenceSlotBlocks_eq_tagged
    (symbols : List encoding.Γ) :
    directSourceFinalBendMixedSemanticOccurrenceSlotBlocks decider symbols =
      directSourceFinalBendTaggedSemanticOccurrenceSlotBlocks
        decider symbols := by
  unfold directSourceFinalBendMixedSemanticOccurrenceSlotBlocks
    directSourceFinalBendTaggedSemanticOccurrenceSlotBlocks
  let formula := directSourceFinalNormalizedFormula decider symbols
  let taggedBends := directSourceFinalBendIndexedTaggedBends decider symbols
  calc
    finalBendSemanticOccurrenceSlotBlocksAt
          directSourceFinalOriginalVariableDecidableEq
          directSourceVariableDecidableEq formula taggedBends =
        finalBendSemanticOccurrenceSlotBlocksAt
          directSourceFinalOriginalVariableDecidableEq
          directSourceFinalOriginalVariableDecidableEq formula taggedBends := by
      exact decidableEq_application_irrel
        (fun equality : DecidableEq Variable =>
          finalBendSemanticOccurrenceSlotBlocksAt
            directSourceFinalOriginalVariableDecidableEq
            equality formula taggedBends)
        directSourceVariableDecidableEq
        directSourceFinalOriginalVariableDecidableEq
    _ = finalBendNamedSemanticOccurrenceSlotBlocksAt
          directSourceFinalOriginalVariableDecidableEq formula taggedBends :=
      finalBendSemanticOccurrenceSlotBlocksAt_eq_named
        directSourceFinalOriginalVariableDecidableEq formula taggedBends

/-- Direct bend semantic slot blocks are exactly the named two-slot blocks
of the indexed untranslated tagged-bend presentation. -/
theorem directSourceFinalBendSemanticOccurrenceSlotBlocks_eq_tagged
    (symbols : List encoding.Γ) :
    directSourceFinalBendSemanticOccurrenceSlotBlocks decider symbols =
      directSourceFinalBendTaggedSemanticOccurrenceSlotBlocks
        decider symbols :=
  (directSourceFinalBendSemanticOccurrenceSlotBlocks_eq_mixed
    decider symbols).trans
      (directSourceFinalBendMixedSemanticOccurrenceSlotBlocks_eq_tagged
        decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
