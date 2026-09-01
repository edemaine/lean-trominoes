/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler

/-! # Semantics of finite variable-incidence prefix blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

noncomputable local instance directFinalGroupedVariablePrefixSemanticsFanInhabited :
    Inhabited VariableRibbonFanData :=
  ⟨variableRibbonFanDataOfCode default⟩

/-- Valid grouped occurrence slots decode to the corresponding finite
variable-site slot. -/
@[simp] theorem groupedVariableFanSiteSlot_genericSlot
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    groupedVariableFanSiteSlot (groupedVariableFanGenericSlot slot) =
      occurrenceVariableSiteSlot slot := by
  cases slot <;> rfl

/-- Every selected local triple contributes exactly three color queries. -/
@[simp] theorem groupedVariableIncidencePrefixQueryBlock_length
    (pair : GroupedVariableFanSlot) :
    (groupedVariableIncidencePrefixQueryBlock pair).length =
      3 * (groupedVariableIncidenceTriples pair).length := by
  unfold groupedVariableIncidencePrefixQueryBlock
  simp [Nat.mul_comm]

/-- The local triple block has the expected ordinary or fixed-red width. -/
theorem groupedVariableIncidenceTriples_length
    (pair : GroupedVariableFanSlot) :
    (groupedVariableIncidenceTriples pair).length =
      match pair.1.kind (groupedVariableFanSiteSlot pair.2) with
      | .fixedRed => 7
      | .fixedGreen | .fixedBlue => 3 := by
  cases kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) <;>
    simp [groupedVariableIncidenceTriples, kindEq,
      allFixedRedTriples, allOrdinaryTriples]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled query stream is the exact pointwise expansion of the
grouped complete fan/active-slot pairs. -/
theorem directSourceFinalGroupedVariableIncidencePrefixQueries_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidencePrefixQueries decider symbols =
      (List.zipWith
        (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
        (directSourceFinalGroupedVariableFanData decider symbols)
        (directSourceFinalGroupedOccurrenceSlots decider symbols)).flatMap
          groupedVariableIncidencePrefixQueryBlock := by
  unfold directSourceFinalGroupedVariableIncidencePrefixQueries
  rw [directSourceFinalGroupedVariableFanSlots_eq_zipWith]

/-- The emitted finite stream consists exactly of one independently
delimited direction word for every query in the grouped expansion. -/
theorem directSourceFinalGroupedVariableIncidencePrefixDirectionTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidencePrefixDirectionTokens
        decider symbols =
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).flatMap
          HorizontalFiniteIncidenceDirectionQuery.block := by
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
