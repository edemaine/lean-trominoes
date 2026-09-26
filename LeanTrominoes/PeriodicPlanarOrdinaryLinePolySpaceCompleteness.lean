/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryEncoding
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.PeriodicPlanarSATLinePolySpaceMembership

/-! # Native PSPACE-completeness of local planar one-dimensional ordinary SAT -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryHardnessStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
set_option maxHeartbeats 400000

def nativeOrdinaryReduction (input : Input) : PeriodicPlanarSAT.Input Nat :=
  nativeOrdinaryInput decider (encoding.encode input)

def nativeOrdinaryReductionCompiler : TM2ComputableInPolyTime encoding.encode
    PeriodicPlanarSAT.FlatEncoding.finEncoding.encode (nativeOrdinaryReduction decider) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (nativeOrdinaryEncodingCompiler decider)
    (fun _ => rfl) (fun _ => rfl)

theorem nativeOrdinaryReduction_correct (input : Input) :
    language input ↔ PeriodicPlanarSAT.Orbit.LocalOneDimensionalProblem (nativeOrdinaryReduction decider input) := by
  rw [nativeOrdinaryReduction, nativeOrdinaryInput_correct, PeriodicCNF.PolySpaceCompiler.formulaOfSymbols_encode]
  exact PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

theorem nativeOrdinaryReduction_three_correct (input : Input) :
    language input ↔ PeriodicPlanarSAT.Orbit.LocalOneDimensionalThreeOccurrenceProblem
      (nativeOrdinaryReduction decider input) := by
  rw [nativeOrdinaryReduction, nativeOrdinaryInput_three_correct, PeriodicCNF.PolySpaceCompiler.formulaOfSymbols_encode]
  exact PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

include decider in
theorem nativeOrdinaryManyOne : Complexity.PolyTimeManyOneReducible encoding PeriodicPlanarSAT.FlatEncoding.finEncoding
    language PeriodicPlanarSAT.Orbit.LocalOneDimensionalProblem := by
  refine ⟨nativeOrdinaryReduction decider, ?_, nativeOrdinaryReduction_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (nativeOrdinaryReductionCompiler decider)⟩

include decider in
theorem nativeOrdinaryManyOneThree : Complexity.PolyTimeManyOneReducible encoding PeriodicPlanarSAT.FlatEncoding.finEncoding
    language PeriodicPlanarSAT.Orbit.LocalOneDimensionalThreeOccurrenceProblem := by
  refine ⟨nativeOrdinaryReduction decider, ?_, nativeOrdinaryReduction_three_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (nativeOrdinaryReductionCompiler decider)⟩

end LeanTrominoes.PeriodicCNFStripReduction

namespace LeanTrominoes.PeriodicPlanarSAT

theorem ordinary_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding Orbit.LocalOneDimensionalProblem := by
  intro Input encoding language h
  obtain ⟨decider⟩ := h
  exact PeriodicCNFStripReduction.nativeOrdinaryManyOne decider

theorem ordinaryThree_PSPACEHard :
    Complexity.PSPACEHard FlatEncoding.finEncoding Orbit.LocalOneDimensionalThreeOccurrenceProblem := by
  intro Input encoding language h
  obtain ⟨decider⟩ := h
  exact PeriodicCNFStripReduction.nativeOrdinaryManyOneThree decider

theorem ordinary_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding Orbit.LocalOneDimensionalProblem :=
  ⟨ordinary_inPSPACE, ordinary_PSPACEHard⟩

theorem ordinaryThree_PSPACEComplete :
    Complexity.PSPACEComplete FlatEncoding.finEncoding Orbit.LocalOneDimensionalThreeOccurrenceProblem :=
  ⟨ordinaryThree_inPSPACE, ordinaryThree_PSPACEHard⟩

end LeanTrominoes.PeriodicPlanarSAT
end
