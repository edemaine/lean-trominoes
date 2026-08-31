/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierOccurrenceSlotBlockFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedClauseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierEqualityData
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance
import LeanTrominoes.RetainedAngularFanFinalCarrierLinkRecordFamilyPresentation

/-! # Semantic occurrence-slot block of one direct final carrier clause -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierSemanticSlotBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierSemanticSlotBlockVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

attribute [local implicit_reducible]
  directSourceFinalStructuralBaseDecidableEq
attribute [local instance]
  directSourceFinalStructuralBaseDecidableEq

private theorem semanticOccurrenceSlot_eq_named
    (symbols : List encoding.Γ)
    (tagged : (EqualityLink CarrierNode × Bool) × Nat)
    (literalIndex : Fin 2) :
    @retainedFinalCoordinatedOccurrenceSlot Variable
        directSourceVariableDecidableEq
        (directSourceFinalNormalizedFormula decider symbols)
        (@finalCarrierNormalizedLiteralAt Variable
          PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          (directSourceFinalNormalizedFormula decider symbols)
          tagged.1 literalIndex)
        tagged.2 literalIndex =
      finalCarrierSemanticOccurrenceSlotAt
        (directThreeCNFSourceFormula decider symbols)
        tagged.1 tagged.2 literalIndex := by
  have formulaEq :
      directSourceFinalNormalizedFormula decider symbols =
        @PeriodicThreeSATThree.formula (ThreeCNFVariable Nat)
          directSourceFinalStructuralBaseDecidableEq
          (directThreeCNFSourceFormula decider symbols) := by
    unfold directSourceFinalNormalizedFormula
    exact decidableEq_application_irrel
      (fun equality : DecidableEq (ThreeCNFVariable Nat) =>
        @PeriodicThreeSATThree.formula (ThreeCNFVariable Nat) equality
          (directThreeCNFSourceFormula decider symbols))
      directSourceFinalOriginalBaseDecidableEq
      directSourceFinalStructuralBaseDecidableEq
  rw [formulaEq]
  unfold finalCarrierSemanticOccurrenceSlotAt
  let formula := PeriodicThreeSATThree.formula
    (directThreeCNFSourceFormula decider symbols)
  calc
    @retainedFinalCoordinatedOccurrenceSlot Variable
        directSourceVariableDecidableEq formula
        (@finalCarrierNormalizedLiteralAt Variable
          PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          formula tagged.1 literalIndex)
        tagged.2 literalIndex =
      @retainedFinalCoordinatedOccurrenceSlot Variable
        directSourceVariableDecidableEq formula
        (@finalCarrierNormalizedLiteralAt Variable
          directSourceVariableDecidableEq formula tagged.1 literalIndex)
        tagged.2 literalIndex := by
      exact decidableEq_application_irrel
        (fun equality : DecidableEq Variable =>
          @retainedFinalCoordinatedOccurrenceSlot Variable
            directSourceVariableDecidableEq formula
            (@finalCarrierNormalizedLiteralAt Variable equality formula
              tagged.1 literalIndex)
            tagged.2 literalIndex)
        PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
        directSourceVariableDecidableEq
    _ = @retainedFinalCoordinatedOccurrenceSlot Variable
        finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq formula
        (@finalCarrierNormalizedLiteralAt Variable
          finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
          formula tagged.1 literalIndex)
        tagged.2 literalIndex := by
      exact decidableEq_application_irrel
        (fun equality : DecidableEq Variable =>
          @retainedFinalCoordinatedOccurrenceSlot Variable equality formula
            (@finalCarrierNormalizedLiteralAt Variable equality formula
              tagged.1 literalIndex)
            tagged.2 literalIndex)
        directSourceVariableDecidableEq
        finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The two normalized literals of one indexed tagged carrier link select
exactly its two named semantic occurrence slots. -/
theorem directSourceFinalCarrierSemanticOccurrenceSlotBlock_eq
    (symbols : List encoding.Γ)
    (tagged : (EqualityLink CarrierNode × Bool) × Nat) :
    (@normalizedCarrierClauseAt Variable
        PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
        (directSourceFinalNormalizedFormula decider symbols)
        tagged.1).zipIdx.map (fun taggedLiteral =>
      retainedFinalCoordinatedOccurrenceSlot
        (directSourceFormula decider symbols)
        taggedLiteral.1 tagged.2 taggedLiteral.2) =
      [finalCarrierSemanticOccurrenceSlotAt
          (directThreeCNFSourceFormula decider symbols)
          tagged.1 tagged.2 0,
        finalCarrierSemanticOccurrenceSlotAt
          (directThreeCNFSourceFormula decider symbols)
          tagged.1 tagged.2 1] := by
  rw [@normalizedCarrierClauseAt_zipIdx_eq_literal_pair Variable
    PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
    (directSourceFinalNormalizedFormula decider symbols) tagged.1]
  simp only [List.map_cons, List.map_nil]
  rw [directSourceFormula_eq_finalNormalized]
  exact congrArg₂ (fun first second => [first, second])
    (semanticOccurrenceSlot_eq_named decider symbols tagged 0)
    (semanticOccurrenceSlot_eq_named decider symbols tagged 1)

end LeanTrominoes.PeriodicCNFStripReduction

end
