/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FirstParentInheritedRouteCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTailDisplacementCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorSourceSemantics
import LeanTrominoes.UnaryFieldBooleanFilterNativeListCompiler

/-! # Compiled first-literal route displacement candidates and selection -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader

private theorem sourceHeaders_append_variables (source : List Token) (count : Nat) :
    sourceHeaders (source ++ List.replicate count .variable) = sourceHeaders source := by
  simp only [sourceHeaders, List.flatMap_append]
  have empty : (List.replicate count Token.variable).flatMap PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.tokenBlock = [] := by
    induction count with
    | zero => rfl
    | succ count _induction => simp [List.replicate_succ, PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.tokenBlock]
  rw [empty, List.append_nil]

private theorem refinementComponent_length (factor : Nat) (source offset : List Nat)
    (aligned : source.length = offset.length) :
    (SignedUnaryCoordinateRefinement.component factor source offset).length = source.length := by
  unfold SignedUnaryCoordinateRefinement.component
  rw [UnaryAlignedAddMachine.sums_length (UnaryAlignedAddMachine.Valid.of_length_eq (by
    simpa only [UnaryFieldConstantScale.values, List.length_map] using aligned))]
  simp only [UnaryFieldConstantScale.values, List.length_map]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance firstParentDisplacementStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
local instance firstParentDisplacementVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq

def directSourceFinalFirstParentRouteControls (symbols : List encoding.Γ) : List Bool :=
  FirstParentInheritedRoute.output (directSourceFinalClauseDescriptors decider symbols)

noncomputable def directSourceFinalFirstParentRouteControlsComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalFirstParentRouteControls decider) := by
  unfold directSourceFinalFirstParentRouteControls
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    FirstParentInheritedRoute.outputComputableInPolyTime

theorem directSourceFinalFirstParentRouteControls_length (symbols : List encoding.Γ) :
    (directSourceFinalFirstParentRouteControls decider symbols).length =
      (directFigureNinePolarityRoutePairs decider symbols).length := by
  rw [directSourceFinalFirstParentRouteControls, FirstParentInheritedRoute.output_length]
  have aligned := congrArg List.length
    (PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail.sourcePairs_map_fst
      (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors (directSourceFormula decider symbols))
      (PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail.tailTables (directSourceFormula decider symbols)))
  have headersEq : sourceHeaders
      (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors (directSourceFormula decider symbols)) =
      sourceHeaders (directSourceFinalClauseDescriptors decider symbols) := by
    rw [directSourceFinalClauseDescriptors_eq_source_prefix, sourceHeaders_append_variables]
  rw [List.length_map, headersEq] at aligned
  exact aligned.symm

def directSourceFinalParentFirstSteps (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  FirstParentInheritedRoute.firstSteps horizontal keepPositive
    (directSourceFinalClauseDescriptors decider symbols)

noncomputable def directSourceFinalParentFirstStepsComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalParentFirstSteps decider horizontal keepPositive) := by
  unfold directSourceFinalParentFirstSteps
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FirstParentInheritedRoute.firstStepsComputableInPolyTime horizontal keepPositive)

theorem directSourceFinalParentFirstSteps_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalParentFirstSteps decider horizontal keepPositive symbols).length =
      (directFigureNinePolarityRoutePairs decider symbols).length := by
  rw [directSourceFinalParentFirstSteps, FirstParentInheritedRoute.firstSteps_length]
  exact directSourceFinalFirstParentRouteControls_length decider symbols

/-- Combine each parent's first step with each row's tail. Only the selected
first-literal rows are used as complete parent-route displacements. -/
def directSourceFinalParentRouteDisplacementCandidates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 1 keepPositive
    (fun positive => directSourceFinalParentFirstSteps decider horizontal positive symbols)
    (fun positive => directSourceFinalTailDisplacements decider horizontal positive symbols)

noncomputable def directSourceFinalParentRouteDisplacementCandidatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalParentRouteDisplacementCandidates decider horizontal keepPositive) := by
  unfold directSourceFinalParentRouteDisplacementCandidates
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 1 keepPositive
    (fun positive => directSourceFinalParentFirstSteps decider horizontal positive)
    (fun positive => directSourceFinalTailDisplacements decider horizontal positive)
    (fun positive symbols => by rw [directSourceFinalParentFirstSteps_length, directSourceFinalParentFirstSteps_length])
    (fun positive symbols => by rw [directSourceFinalTailDisplacements_length, directSourceFinalParentFirstSteps_length])
    (fun positive => directSourceFinalParentFirstStepsComputableInPolyTime decider horizontal positive)
    (fun positive => directSourceFinalTailDisplacementsComputableInPolyTime decider horizontal positive)

theorem directSourceFinalParentRouteDisplacementCandidates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalParentRouteDisplacementCandidates decider horizontal keepPositive symbols).length =
      (directFigureNinePolarityRoutePairs decider symbols).length := by
  have aligned : ∀ positive,
      (directSourceFinalParentFirstSteps decider horizontal positive symbols).length =
        (directSourceFinalTailDisplacements decider horizontal positive symbols).length := by
    intro positive
    rw [directSourceFinalParentFirstSteps_length, directSourceFinalTailDisplacements_length]
  unfold directSourceFinalParentRouteDisplacementCandidates SignedUnaryCoordinateRefinement.values
  rw [UnaryAlignedDifference.values_length, refinementComponent_length _ _ _ (aligned true),
    refinementComponent_length _ _ _ (aligned false), directSourceFinalParentFirstSteps_length,
    directSourceFinalParentFirstSteps_length, Nat.min_self]

def directSourceFinalFirstParentRouteDisplacements (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldBooleanFilter.selectedValues (directSourceFinalFirstParentRouteControls decider symbols)
    (directSourceFinalParentRouteDisplacementCandidates decider horizontal keepPositive symbols)

/-- The selected displacement column is compiled from direct symbols,
including empty alphabets, using the same row controls as coordinate lookup. -/
noncomputable def directSourceFinalFirstParentRouteDisplacementsComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFirstParentRouteDisplacements decider horizontal keepPositive) := by
  unfold directSourceFinalFirstParentRouteDisplacements
  exact UnaryFieldBooleanFilter.selectedValuesNativeListComputableInPolyTime (directSourceFinalFirstParentRouteControls decider)
    (directSourceFinalParentRouteDisplacementCandidates decider horizontal keepPositive)
    (directSourceFinalFirstParentRouteControlsComputableInPolyTime decider)
    (directSourceFinalParentRouteDisplacementCandidatesComputableInPolyTime decider horizontal keepPositive)

end LeanTrominoes.PeriodicCNFStripReduction
end
