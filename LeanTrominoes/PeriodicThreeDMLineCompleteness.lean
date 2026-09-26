/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMLineMembership
import LeanTrominoes.PeriodicThreeDMLineHardness

/-! # Native PSPACE completeness for local horizontal degree-two-or-three 3DM

This endpoint omits the supplied drawing. The planar supplied-drawing upper
bound additionally needs the native finite drawing verifier.
-/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM
open Turing PeriodicCNFStripReduction
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
set_option synthInstance.maxSize 2048

def nativeProblemEncodingCompilerTotal : TM2ComputableInPolyTime id FlatEncoding.finEncoding.encode
    (nativeThreeDMProblem decider) := by
  classical
  by_cases h : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice h⟩
    exact nativeThreeDMProblemEncodingCompiler decider
  · letI : IsEmpty encoding.Γ := ⟨fun x => h ⟨x⟩⟩
    letI : Inhabited FlatEncoding.finEncoding.Γ := ⟨.bit0⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime FlatEncoding.finEncoding.encode _

def localLineReduction (x : Input) : PeriodicThreeDM := nativeThreeDMProblem decider (encoding.encode x)

def localLineReductionCompiler : TM2ComputableInPolyTime encoding.encode FlatEncoding.finEncoding.encode
    (localLineReduction decider) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (nativeProblemEncodingCompilerTotal decider)
    (fun _ => rfl) (fun _ => rfl)

theorem localLineReduction_correct (x : Input) : language x ↔ LocalLineProblem (localLineReduction decider x) := by
  have full := localPlanarLineReduction_correct decider x
  apply full.trans
  change (LocalLineProblem (localLineReduction decider x) ∧
    FiniteDrawingCertificate.verifies (nativeThreeDMProblem decider (encoding.encode x))
      (nativeThreeDMUnitDrawing decider (encoding.encode x)) = true) ↔ _
  simp only [nativeThreeDMUnit_verified,and_true]

include decider in
theorem localLineManyOne : Complexity.PolyTimeManyOneReducible encoding FlatEncoding.finEncoding language LocalLineProblem := by
  refine ⟨localLineReduction decider,?_,localLineReduction_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (localLineReductionCompiler decider)⟩

theorem localLineProblem_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding LocalLineProblem := by
  intro Input encoding language hs
  obtain ⟨decider⟩ := hs
  exact localLineManyOne decider

theorem localLineProblem_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding LocalLineProblem :=
  ⟨localLineProblem_inPSPACE,localLineProblem_PSPACEHard⟩

end LeanTrominoes.PeriodicThreeDM
end
