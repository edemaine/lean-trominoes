/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeSATThreePolyTimeCompiler
import LeanTrominoes.PeriodicThreeSATThreePolySpaceMembership

/-! # Native flat-encoded PSPACE-completeness of local 1D 3SAT-3 -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeSATThree.PolyTime
open Computability Turing PeriodicCNF
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def reduction (input : Input) : PeriodicCNF Nat := formula decider (encoding.encode input)

theorem reduction_correct (input : Input) :
    language input ↔ LocalPeriodicThreeSATThree1DSAT (reduction decider input) := by
  let original := PolySpaceReduction.formula decider input
  have sourceEq : source decider (encoding.encode input)=original :=
    PolySpaceCompiler.formulaOfSymbols_encode decider input
  have origForward : original.IsForwardLocal := by
    unfold original PolySpaceReduction.formula
    exact BoundedMachineAtom.designatedMachinePeriodicCNF_forward _ _
  have origOne := isOneDimensional_of_isForwardLocal origForward
  have origLocal := isLocalOnLine_of_isForwardLocal origForward
  have targetEq : reduction decider input=Numeric.formula original := by
    unfold reduction formula
    rw [sourceEq]
  have targetForward := Numeric.forward original origForward
  have targetOne := isOneDimensional_of_isForwardLocal targetForward
  have targetLocal := isLocalOnLine_of_isForwardLocal targetForward
  have targetWidth := Numeric.width_three original (PolySpaceHardness.reduction_width_three decider input)
  have sat : (Numeric.formula original).SatisfiableOnLine ↔ original.SatisfiableOnLine := by
    rw [← satisfiable_iff_satisfiableOnLine targetOne,Numeric.satisfiable_iff,
      satisfiable_iff_satisfiableOnLine origOne]
  rw [PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input]
  rw [targetEq]
  simp only [LocalPeriodicThreeSATThree1DSAT,LocalPeriodicThreeCNF1DSAT,LocalPeriodicCNF1DSAT,
    Numeric.occurrences_three,targetWidth,targetOne,targetLocal,true_and,sat]
  change original.IsOneDimensional ∧ original.IsLocalOnLine ∧ original.SatisfiableOnLine ↔ original.SatisfiableOnLine
  simp only [origOne,origLocal,true_and]

noncomputable def reductionComputableInPolyTime :
    TM2ComputableInPolyTime encoding.encode PeriodicCNFFlatEncoding.finEncoding.encode (reduction decider) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (formulaComputableInPolyTime decider)
    (fun _ => rfl) (fun _ => rfl)

include decider in
theorem manyOne : Complexity.PolyTimeManyOneReducible encoding PeriodicCNFFlatEncoding.finEncoding
    language LocalPeriodicThreeSATThree1DSAT := by
  refine ⟨reduction decider,?_,reduction_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
    (reductionComputableInPolyTime decider)⟩

end LeanTrominoes.PeriodicThreeSATThree.PolyTime

namespace LeanTrominoes.PeriodicCNF.PolySpaceHardness

theorem localPeriodicThreeSATThree1DSAT_PSPACEHard :
    Complexity.PSPACEHard PeriodicCNFFlatEncoding.finEncoding LocalPeriodicThreeSATThree1DSAT := by
  intro Input encoding language h
  obtain ⟨decider⟩ := h
  exact PeriodicThreeSATThree.PolyTime.manyOne decider

theorem localPeriodicThreeSATThree1DSAT_PSPACEComplete :
    Complexity.PSPACEComplete PeriodicCNFFlatEncoding.finEncoding LocalPeriodicThreeSATThree1DSAT :=
  ⟨localPeriodicThreeSATThree1DSAT_inPSPACE,localPeriodicThreeSATThree1DSAT_PSPACEHard⟩

end LeanTrominoes.PeriodicCNF.PolySpaceHardness
end
