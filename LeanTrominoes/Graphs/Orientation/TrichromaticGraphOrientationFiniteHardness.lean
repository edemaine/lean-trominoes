/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.Reduction.Program.ProgramGraphOrientationFiniteEncoding
import LeanTrominoes.Complexity.FiniteNPProgramSource
import LeanTrominoes.Computation.TM2.TM2EmptyAlphabetListInputCompiler

/-! # Native NP hardness of ordinary finite colored graph orientation -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation
open Turing PeriodicCNFStripReduction
variable {Source : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Source} {language : Source → Prop}
variable (source : PeriodicCNF.ProgramSource encoding language)
variable (zero : ∀ symbols, FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def programFiniteEncodingCompilerTotal : TM2ComputableInPolyTime id FlatEncoding.finEncoding.encode
    (programOrientationGraph source) := by
  classical
  by_cases h : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice h⟩
    exact programOrientationFiniteEncodingCompiler source zero
  · letI : IsEmpty encoding.Γ := ⟨fun x => h ⟨x⟩⟩
    letI : Inhabited FlatEncoding.finEncoding.Γ := ⟨.bit0⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime FlatEncoding.finEncoding.encode _

def finiteReduction (input : Source) : Input := programOrientationGraph source (encoding.encode input)

def finiteReductionCompiler : TM2ComputableInPolyTime encoding.encode FlatEncoding.finEncoding.encode
    (finiteReduction source) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (programFiniteEncodingCompilerTotal source zero)
    (fun _ => rfl) (fun _ => rfl)

include zero in
theorem finiteReduction_correct (input : Source) : language input ↔ FiniteProblem (finiteReduction source input) := by
  rw [finiteReduction,programOrientationGraph_finite_correct source zero]
  exact source.correct input

include zero in
theorem finiteManyOne : Complexity.PolyTimeManyOneReducible encoding FlatEncoding.finEncoding language FiniteProblem := by
  refine ⟨finiteReduction source,?_,finiteReduction_correct source zero⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (finiteReductionCompiler source zero)⟩

theorem finiteProblem_npHard : Complexity.NPHard FlatEncoding.finEncoding FiniteProblem := by
  intro Source encoding language member
  obtain ⟨verifier⟩ := member
  exact finiteManyOne (FiniteNPProgramSource.source verifier) (FiniteNPProgramSource.formula_zero verifier)

end LeanTrominoes.TrichromaticGraphOrientation
end
