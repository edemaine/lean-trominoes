/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMEncoding
import LeanTrominoes.PeriodicThreeDMPlanarLineDecision
import LeanTrominoes.PeriodicCNFStripNativeThreeDMLocality
import LeanTrominoes.PeriodicCNFStripNativeThreeDMVerification
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Native PSPACE hardness of local planar one-dimensional periodic 3DM

The binary input contains the entire instance and its supplied drawing. The
predicate checks degree two or three, graph locality, horizontal offsets, and
the finite continuous-planarity certificate before asking for a matching.
-/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM
open Turing PeriodicCNFStripReduction

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048


def nativeThreeDMPlanarEncodingCompilerTotal : TM2ComputableInPolyTime id FlatEncoding.Planar.finEncoding.encode
    (nativeThreeDMPlanarInput decider) := by
  classical
  by_cases h : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice h⟩
    exact nativeThreeDMPlanarEncodingCompiler decider
  · letI : IsEmpty encoding.Γ := ⟨fun x => h ⟨x⟩⟩
    letI : Inhabited FlatEncoding.Planar.finEncoding.Γ := ⟨.bit0⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime FlatEncoding.Planar.finEncoding.encode _

theorem nativeThreeDMPlanarInput_correct (s : List encoding.Γ) :
    LocalPlanarLineProblem (nativeThreeDMPlanarInput decider s) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) := by
  have correct : (nativeThreeDMProblem decider s).Satisfiable ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) := by
    rw [nativeThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
    exact (problem_correct _).symm
  constructor
  · intro h
    exact correct.mp h.1.2.2.2.2
  · intro h
    exact ⟨⟨nativeThreeDMWellFormed decider s,nativeThreeDMDegree decider s,
      nativeThreeDM_horizontal decider s,nativeThreeDM_local decider s,correct.mpr h⟩,
      nativeThreeDMUnit_verified decider s⟩

def localPlanarLineReduction (input : Input) : NormalizationCompiler.Input :=
  nativeThreeDMPlanarInput decider (encoding.encode input)

def localPlanarLineReductionCompiler : TM2ComputableInPolyTime encoding.encode FlatEncoding.Planar.finEncoding.encode
    (localPlanarLineReduction decider) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (nativeThreeDMPlanarEncodingCompilerTotal decider)
    (fun _ => rfl) (fun _ => rfl)

theorem localPlanarLineReduction_correct (input : Input) :
    language input ↔ LocalPlanarLineProblem (localPlanarLineReduction decider input) := by
  rw [localPlanarLineReduction,nativeThreeDMPlanarInput_correct,PeriodicCNF.PolySpaceCompiler.formulaOfSymbols_encode]
  exact PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

include decider in
theorem localPlanarLineManyOne : Complexity.PolyTimeManyOneReducible encoding FlatEncoding.Planar.finEncoding
    language LocalPlanarLineProblem := by
  refine ⟨localPlanarLineReduction decider,?_,localPlanarLineReduction_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (localPlanarLineReductionCompiler decider)⟩

theorem localPlanarLineProblem_PSPACEHard : Complexity.PSPACEHard FlatEncoding.Planar.finEncoding LocalPlanarLineProblem := by
  intro Input encoding language hs
  obtain ⟨decider⟩ := hs
  exact localPlanarLineManyOne decider

end LeanTrominoes.PeriodicThreeDM
end
