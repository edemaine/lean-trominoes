/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFPolySpaceHardness

/-! # Encoded polynomial-time hardness of local one-dimensional 3SAT

The existing machine reduction already produces width-three Tseitin clauses.
Its verified polynomial-time compiler therefore proves this stronger endpoint
without an additional clause-splitting compiler.
-/
namespace LeanTrominoes.PeriodicCNF

def LocalPeriodicThreeCNF1DSAT (f : PeriodicCNF Nat) : Prop :=
  f.WidthAtMost 3 ∧ LocalPeriodicCNF1DSAT f

namespace PolySpaceHardness
open Turing
variable {Input : Type} {encoding : Computability.FinEncoding Input} {language : Input → Prop}

noncomputable section
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

noncomputable local instance (decider : Complexity.DeciderInPolySpace encoding language)
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

theorem reduction_width_three (decider : Complexity.DeciderInPolySpace encoding language) (input : Input) :
    (PolySpaceReduction.formula decider input).WidthAtMost 3 := by
  unfold PolySpaceReduction.formula BoundedMachineAtom.designatedMachinePeriodicCNF
  exact requireTransitionExpr_widthAtMost_three _ _

theorem threeCNF_directPolyTimeManyOneReducible (decider : Complexity.DeciderInPolySpace encoding language) :
    Complexity.PolyTimeManyOneReducible encoding PeriodicCNFFlatEncoding.finEncoding
      language LocalPeriodicThreeCNF1DSAT := by
  refine ⟨PolySpaceReduction.formula decider,?_,?_⟩
  · exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
      (directReductionComputableInPolyTime decider)⟩
  · intro input
    rw [LocalPeriodicThreeCNF1DSAT,and_iff_right (reduction_width_three decider input)]
    exact PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

theorem localPeriodicThreeCNF1DSAT_PSPACEHard :
    Complexity.PSPACEHard PeriodicCNFFlatEncoding.finEncoding LocalPeriodicThreeCNF1DSAT := by
  intro Input encoding language h
  obtain ⟨decider⟩ := h
  exact threeCNF_directPolyTimeManyOneReducible decider

end
end PolySpaceHardness
end LeanTrominoes.PeriodicCNF
