/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case0
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case1
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case2
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case3
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case4
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case5
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case6
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case7
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case8
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case9
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case10
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case11
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case12
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case13
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case14
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case15
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case16
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case17
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case18
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificates.Case19

/-! # One inherited first-literal route per parent clause -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open HorizontalRoutedRouteHeader HorizontalRoutedRouteHeaderPresentationAtomScope

private theorem firstParentSelectorCheck_first_correct
    (first : LeanTrominoes.PeriodicCNF.UnaryProgramClauseProfile.LiteralProfile)
    (direction : AxisDirection) : firstDirectedProfileCheck firstParentSelectorCheck first direction = true := by
  rcases first with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value <;> cases direction
  · exact firstParentSelectorCheck_case0
  · exact firstParentSelectorCheck_case1
  · exact firstParentSelectorCheck_case2
  · exact firstParentSelectorCheck_case3
  · exact firstParentSelectorCheck_case4
  · exact firstParentSelectorCheck_case5
  · exact firstParentSelectorCheck_case6
  · exact firstParentSelectorCheck_case7
  · exact firstParentSelectorCheck_case8
  · exact firstParentSelectorCheck_case9
  · exact firstParentSelectorCheck_case10
  · exact firstParentSelectorCheck_case11
  · exact firstParentSelectorCheck_case12
  · exact firstParentSelectorCheck_case13
  · exact firstParentSelectorCheck_case14
  · exact firstParentSelectorCheck_case15
  · exact firstParentSelectorCheck_case16
  · exact firstParentSelectorCheck_case17
  · exact firstParentSelectorCheck_case18
  · exact firstParentSelectorCheck_case19

private theorem firstParentSelectorCheck_correct (profile : DirectedClauseProfile) :
    firstParentSelectorCheck profile = true :=
  firstDirectedProfileCheck_sound firstParentSelectorCheck firstParentSelectorCheck_first_correct profile

/-- Every finite parent profile has an actual eligible route row. -/
theorem index_lt : ∀ profile : DirectedClauseProfile,
    index profile < (sourceClauseHeaders profile).length := by
  intro profile
  have checked := firstParentSelectorCheck_correct profile
  simp only [firstParentSelectorCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1

theorem selectedHeader_eligible : ∀ profile : DirectedClauseProfile,
    eligible profile (selectedHeader profile) = true := by
  intro profile
  have checked := firstParentSelectorCheck_correct profile
  simp only [firstParentSelectorCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.2

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
