/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationNativeEncoding
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationLineMembership
import LeanTrominoes.Computation.TM2.TM2EmptyAlphabetListInputCompiler

/-! # Native PSPACE completeness of ordinary local one-dimensional orientation -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation
open Turing PeriodicCNFStripReduction
variable {Source : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Source} {language : Source → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def nativeOrientationEncodingCompilerTotal : TM2ComputableInPolyTime id FlatEncoding.finEncoding.encode
    (nativeOrientationGraph decider) := by
  classical
  by_cases h : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice h⟩
    exact nativeOrientationEncodingCompiler decider
  · letI : IsEmpty encoding.Γ := ⟨fun x => h ⟨x⟩⟩
    letI : Inhabited FlatEncoding.finEncoding.Γ := ⟨.bit0⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime FlatEncoding.finEncoding.encode _

def localLineReduction (input : Source) : Input :=
  nativeOrientationGraph decider (encoding.encode input)

def localLineReductionCompiler : TM2ComputableInPolyTime encoding.encode FlatEncoding.finEncoding.encode
    (localLineReduction decider) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (nativeOrientationEncodingCompilerTotal decider)
    (fun _ => rfl) (fun _ => rfl)

theorem localLineReduction_correct (input : Source) :
    language input ↔ LocalLineProblem (localLineReduction decider input) := by
  rw [localLineReduction,nativeOrientationGraph_correct,PeriodicCNF.PolySpaceCompiler.formulaOfSymbols_encode]
  exact PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

include decider in
theorem localLineManyOne : Complexity.PolyTimeManyOneReducible encoding FlatEncoding.finEncoding
    language LocalLineProblem := by
  refine ⟨localLineReduction decider,?_,localLineReduction_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (localLineReductionCompiler decider)⟩

theorem localLineProblem_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding LocalLineProblem := by
  intro Source encoding language source
  obtain ⟨decider⟩ := source
  exact localLineManyOne decider

theorem localLineProblem_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding LocalLineProblem :=
  ⟨localLineProblem_inPSPACE,localLineProblem_PSPACEHard⟩

end LeanTrominoes.TrichromaticGraphOrientation
end
