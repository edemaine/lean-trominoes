/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderPresentationAtomScopeCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.SignedUnaryCoordinateRefinementCompiler

/-! # One inherited first-literal route per parent clause -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open HorizontalRoutedRouteHeader HorizontalRoutedRouteHeaderPresentationAtomScope

/-- The same row must carry both the inherited atom and its source route. -/
def eligible (profile : DirectedClauseProfile) (header : Header) : Bool :=
  match header.figurePrefix with
  | .local _ => false
  | .inherited slot _ =>
    decide (presentationSlotAt profile slot = .first) &&
      decide (remapScopeControl profile (outputAtomScopeControl header) = .inherited .first)

def index (profile : DirectedClauseProfile) : Nat :=
  (sourceClauseHeaders profile).findIdx (eligible profile)

def selectedHeader (profile : DirectedClauseProfile) : Header :=
  (sourceClauseHeaders profile).getD (index profile) default

/-- Every finite parent profile has an actual eligible route row. -/
theorem index_lt : ∀ profile : DirectedClauseProfile,
    index profile < (sourceClauseHeaders profile).length := by
  native_decide

theorem selectedHeader_eligible : ∀ profile : DirectedClauseProfile,
    eligible profile (selectedHeader profile) = true := by
  native_decide

/-- Exactly one selector bit per final occurrence row, at the first eligible row. -/
def controls (profile : DirectedClauseProfile) : List Bool :=
  (List.range (sourceClauseHeaders profile).length).map fun row => decide (row = index profile)

@[simp] theorem controls_length (profile : DirectedClauseProfile) :
    (controls profile).length = (sourceClauseHeaders profile).length := by
  simp [controls]

theorem controls_count_true : ∀ profile : DirectedClauseProfile,
    (controls profile).count true = 1 := by
  intro profile
  have count : (List.range (sourceClauseHeaders profile).length).count (index profile) = 1 := by
    rw [List.count_range]
    simp only [index_lt, ↓reduceIte]
  simpa [controls, List.count_eq_countP, List.countP_map, Bool.beq_eq_decide_eq, Function.comp_def] using count

/-- The original presentation's first literal determines its route direction. -/
def firstDirection (profile : DirectedClauseProfile) : AxisDirection :=
  (profile.taggedLiterals.headD (⟨false, false⟩, .invalid)).2

def controlBlock : Token → List Bool
  | .variable => []
  | .clause profile => controls profile

def output (source : List Token) : List Bool := source.flatMap controlBlock

noncomputable def outputComputableInPolyTime : TM2ComputableInPolyTime id id output :=
  FiniteBlockTransducer.computableInPolyTime controlBlock

theorem output_length (source : List Token) :
    (output source).length = (sourceHeaders source).length := by
  simp only [output, sourceHeaders, List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro token _member
  cases token <;> simp [controlBlock, PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.tokenBlock]

/-- Repeat each parent's first-direction component in its complete row block. -/
def firstStepBlock (horizontal keepPositive : Bool) : Token → List Nat
  | .variable => []
  | .clause profile => List.replicate (sourceClauseHeaders profile).length
      (SignedUnaryCoordinateRefinement.field keepPositive
        (if horizontal then (firstDirection profile).step.1 else (firstDirection profile).step.2))

def firstSteps (horizontal keepPositive : Bool) (source : List Token) : List Nat :=
  source.flatMap (firstStepBlock horizontal keepPositive)

noncomputable def firstStepsComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (firstSteps horizontal keepPositive) := by
  let physical := FiniteBlockTransducer.computableInPolyTime
    (fun token => UnaryFieldEncoderMachine.unaryFields (firstStepBlock horizontal keepPositive token))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro source
  simp only [firstSteps, UnaryFieldEncoderMachine.unaryFields, List.flatMap_assoc, id_eq]

theorem firstSteps_length (horizontal keepPositive : Bool) (source : List Token) :
    (firstSteps horizontal keepPositive source).length = (output source).length := by
  simp only [firstSteps, output, List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro token _member
  cases token <;> simp [firstStepBlock, controlBlock]

end LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
end
