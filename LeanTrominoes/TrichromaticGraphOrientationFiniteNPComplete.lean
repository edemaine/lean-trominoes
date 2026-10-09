/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFiniteInNP
import LeanTrominoes.TrichromaticGraphOrientationFiniteHardness
import LeanTrominoes.TrichromaticGraphOrientationUnaryCompiler

/-! # Ordinary finite colored graph orientation is NP complete -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation
open Turing PeriodicCNFStripReduction
variable {Source : Type} {encoding : _root_.Computability.FinEncoding Source} {language : Source → Prop}
variable (source : PeriodicCNF.ProgramSource encoding language)
variable (zero : ∀ symbols, FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def programFiniteUnaryCompilerTotal : TM2ComputableInPolyTime id UnaryEncoding.finEncoding.encode
    (programOrientationGraph source) := by
  classical
  by_cases h : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice h⟩
    exact UnaryEncoding.encodingCompiler (graph := programOrientationGraph source)
      (programOrientationFiniteFieldsCompiler source zero)
  · letI : IsEmpty encoding.Γ := ⟨fun x => h ⟨x⟩⟩
    letI : Inhabited UnaryEncoding.finEncoding.Γ := ⟨.unit⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryEncoding.finEncoding.encode _

def finiteUnaryReductionCompiler : TM2ComputableInPolyTime encoding.encode UnaryEncoding.finEncoding.encode
    (finiteReduction source) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (programFiniteUnaryCompilerTotal source zero)
    (fun _ => rfl) (fun _ => rfl)

include zero in
theorem finiteUnaryManyOne : Complexity.PolyTimeManyOneReducible encoding UnaryEncoding.finEncoding language FiniteProblem := by
  refine ⟨finiteReduction source,?_,finiteReduction_correct source zero⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (finiteUnaryReductionCompiler source zero)⟩

theorem finiteProblem_unary_npHard : Complexity.NPHard UnaryEncoding.finEncoding FiniteProblem := by
  intro Source encoding language member
  obtain ⟨verifier⟩ := member
  exact finiteUnaryManyOne (FiniteNPProgramSource.source verifier) (FiniteNPProgramSource.formula_zero verifier)

theorem finiteProblem_unary_npComplete : Complexity.NPComplete UnaryEncoding.finEncoding FiniteProblem :=
  ⟨finiteProblem_unary_inNP,finiteProblem_unary_npHard⟩

end LeanTrominoes.TrichromaticGraphOrientation
end
