/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierEqualityData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartSemantics
import LeanTrominoes.RetainedAngularFanFinalBendLookupSemantics
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Generic indexed presentation of the direct final-bend family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendIndexedPresentationStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalOriginalBaseDecidableEq
attribute [local instance]
  directSourceFinalOriginalBaseDecidableEq

local instance directFinalBendIndexedPresentationVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalOriginalVariableDecidableEq

private theorem directSourceFinalCarrierClauses_eq_metadata
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierClauses decider symbols =
      PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
        (directThreeCNFSourceFormula decider symbols) := by
  rfl

/-- The named direct bend start is the generic crossover-plus-carrier prefix
length. -/
theorem directSourceFinalBendStart_eq_generic
    (symbols : List encoding.Γ) :
    directSourceFinalBendStart decider symbols =
      (crossoverMetadataNormalizedClausesDedup
        (PeriodicThreeSATThree.formula
          (directThreeCNFSourceFormula decider symbols))).length +
      (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
        (directThreeCNFSourceFormula decider symbols)).length := by
  have carrierStartEq :
      directSourceFinalCarrierStart decider symbols =
        directSourceFinalCarrierStartFamily decider symbols
          directSourceFinalOriginalVariableDecidableEq := by
    calc
      _ = directSourceFinalCarrierStructuralStart decider symbols :=
        (directSourceFinalCarrierStart_structural decider symbols).eq
      _ = _ := by
        unfold directSourceFinalCarrierStructuralStart
        exact congrArg
          (directSourceFinalCarrierStartFamily decider symbols)
          (Subsingleton.elim _ _)
  unfold directSourceFinalBendStart
  rw [carrierStartEq, directSourceFinalCarrierClauses_eq_metadata]
  rfl

/-- Every member of the named indexed bend presentation satisfies the generic
final-bend index relation. -/
theorem directSourceFinalBendIndexedPresentation_indexed
    (symbols : List encoding.Γ) :
    ∀ tagged ∈
        ((baseRouteBends
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))).product
            [true, false]).zipIdx
          (directSourceFinalBendStart decider symbols),
      finalBendTaggedBendIndexed
        (directThreeCNFSourceFormula decider symbols) tagged.1 tagged.2 := by
  intro tagged taggedMember
  let source := directThreeCNFSourceFormula decider symbols
  let retained := PeriodicThreeSATThree.formula source
  let carrierLength :=
    (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
      source).length
  let indexedWith (equality : DecidableEq Variable) : Prop :=
    (tagged.1, tagged.2) ∈
      ((@baseRouteBends Variable equality retained).product
        [true, false]).zipIdx
          ((@crossoverMetadataNormalizedClausesDedup Variable equality
            retained).length + carrierLength)
  have originalIndexed :
      indexedWith directSourceFinalOriginalVariableDecidableEq := by
    unfold indexedWith
    rw [← directSourceFinalBendStart_eq_generic decider symbols]
    exact taggedMember
  let derivedEquality : DecidableEq Variable :=
    @PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
      (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq
  have equalityIrrel := decidableEq_application_irrel indexedWith
    directSourceFinalOriginalVariableDecidableEq derivedEquality
  unfold finalBendTaggedBendIndexed
  dsimp only
  change indexedWith derivedEquality
  exact equalityIrrel.symm ▸ originalIndexed

end LeanTrominoes.PeriodicCNFStripReduction

end
