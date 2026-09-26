/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativePlanarLocality
import LeanTrominoes.PeriodicCNFStripNativePlanarGridBound
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.PeriodicPlanarSATLinePolySpaceMembership

/-! # Native PSPACE-completeness of local planar one-dimensional exact-one SAT -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeHardnessStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
set_option maxHeartbeats 400000

theorem nativePlanarInput_correct (s : List encoding.Γ) :
    PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneProblem (nativePlanarInput decider s) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) := by
  simp only [PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneProblem, PeriodicPlanarSAT.Unbounded.ExactOneProblem,
    PeriodicPlanarSAT.Unbounded.Valid, nativePlanarInput_oneDimensional, nativePlanarInput_gridBound,
    nativePlanarInput_local, nativePlanarInput_width, nativePlanarInput_compatible,
    nativePlanarInput_planar, true_and]
  exact nativePlanarInput_exactOne decider s

theorem nativePlanarInput_three_correct (s : List encoding.Γ) :
    PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem (nativePlanarInput decider s) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) := by
  simp only [PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.ExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.ExactOneProblem, PeriodicPlanarSAT.Unbounded.Valid,
    nativePlanarInput_oneDimensional, nativePlanarInput_gridBound, nativePlanarInput_local,
    nativePlanarInput_occurrences, nativePlanarInput_width, nativePlanarInput_compatible,
    nativePlanarInput_planar, true_and]
  exact nativePlanarInput_exactOne decider s

def nativePlanarReduction (input : Input) : PeriodicPlanarSAT.Input Nat :=
  nativePlanarInput decider (encoding.encode input)

def nativePlanarReductionCompiler : TM2ComputableInPolyTime encoding.encode
    PeriodicPlanarSAT.FlatEncoding.finEncoding.encode (nativePlanarReduction decider) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (nativePlanarEncodingCompiler decider)
    (fun _ => rfl) (fun _ => rfl)

theorem nativePlanarReduction_correct (input : Input) :
    language input ↔ PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneProblem (nativePlanarReduction decider input) := by
  rw [nativePlanarReduction, nativePlanarInput_correct, PeriodicCNF.PolySpaceCompiler.formulaOfSymbols_encode]
  exact PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

theorem nativePlanarReduction_three_correct (input : Input) :
    language input ↔ PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem
      (nativePlanarReduction decider input) := by
  rw [nativePlanarReduction, nativePlanarInput_three_correct, PeriodicCNF.PolySpaceCompiler.formulaOfSymbols_encode]
  exact PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

include decider in
theorem nativePlanarManyOne : Complexity.PolyTimeManyOneReducible encoding PeriodicPlanarSAT.FlatEncoding.finEncoding
    language PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneProblem := by
  refine ⟨nativePlanarReduction decider, ?_, nativePlanarReduction_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (nativePlanarReductionCompiler decider)⟩

include decider in
theorem nativePlanarManyOneThree : Complexity.PolyTimeManyOneReducible encoding PeriodicPlanarSAT.FlatEncoding.finEncoding
    language PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem := by
  refine ⟨nativePlanarReduction decider, ?_, nativePlanarReduction_three_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (nativePlanarReductionCompiler decider)⟩

end LeanTrominoes.PeriodicCNFStripReduction

namespace LeanTrominoes.PeriodicPlanarSAT

theorem exactOne_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding Unbounded.LocalOneDimensionalExactOneProblem := by
  intro Input encoding language h
  obtain ⟨decider⟩ := h
  exact PeriodicCNFStripReduction.nativePlanarManyOne decider

theorem exactOneThree_PSPACEHard :
    Complexity.PSPACEHard FlatEncoding.finEncoding Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem := by
  intro Input encoding language h
  obtain ⟨decider⟩ := h
  exact PeriodicCNFStripReduction.nativePlanarManyOneThree decider

theorem exactOne_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding Unbounded.LocalOneDimensionalExactOneProblem :=
  ⟨exactOne_inPSPACE, exactOne_PSPACEHard⟩

theorem exactOneThree_PSPACEComplete :
    Complexity.PSPACEComplete FlatEncoding.finEncoding Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem :=
  ⟨exactOneThree_inPSPACE, exactOneThree_PSPACEHard⟩

end LeanTrominoes.PeriodicPlanarSAT
end
