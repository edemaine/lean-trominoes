/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicComputationTrace
import LeanTrominoes.PeriodicCNFMachineConfiguration
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting bounded machine configurations

A configuration whose stacks have a fixed width is injected into its finite
canonical Boolean slice.  A terminating deterministic computation cannot
repeat a configuration, so its number of steps is strictly below the number
of such slices.  This supplies the polynomial-width reset clock used by the
PSPACE-hardness reduction.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- Number of Boolean source atoms needed for a bounded configuration, with
no clock bits included. -/
def configurationBitCount : Nat :=
  atomCount (tm := tm) (space := space) (clockBits := 0)

/-- Finite canonical Boolean code of a bounded configuration. -/
def configurationBits (configuration : tm.Cfg) :
    Fin (configurationBitCount (tm := tm) (space := space)) → Bool :=
  fun atom => encode (space := space) (clockBits := 0)
    (⟨0, configuration⟩ : PeriodicComputation.ResetClockState tm.Cfg) atom.val

private theorem encode_eq_of_configurationBits_eq
    {first second : tm.Cfg}
    (bitsEq : configurationBits (space := space) first =
      configurationBits (space := space) second) :
    encode (space := space) (clockBits := 0)
        (⟨0, first⟩ : PeriodicComputation.ResetClockState tm.Cfg) =
      encode (space := space) (clockBits := 0)
        (⟨0, second⟩ : PeriodicComputation.ResetClockState tm.Cfg) := by
  funext atom
  by_cases atomLt : atom < configurationBitCount (tm := tm) (space := space)
  · have bitEq := congrFun bitsEq ⟨atom, atomLt⟩
    exact bitEq
  · have atomLt' : ¬ atom < atomCount (tm := tm) (space := space)
        (clockBits := 0) := atomLt
    simp [encode, atomLt']

/-- Canonical finite configuration bits are injective among configurations
whose stacks fit the selected width. -/
theorem configurationBits_injective_of_stacksFit
    {first second : tm.Cfg}
    (firstFits : ∀ stack, (first.stk stack).length ≤ space)
    (secondFits : ∀ stack, (second.stk stack).length ≤ space)
    (bitsEq : configurationBits (space := space) first =
      configurationBits (space := space) second) :
    first = second := by
  let firstState : PeriodicComputation.ResetClockState tm.Cfg := ⟨0, first⟩
  let secondState : PeriodicComputation.ResetClockState tm.Cfg := ⟨0, second⟩
  have encodeEq := encode_eq_of_configurationBits_eq bitsEq
  have decodeEq := congrArg
    (fun valuation =>
      (decode (tm := tm) (space := space) (clockBits := 0)
        valuation).toCfg) encodeEq
  change (decode (tm := tm) (space := space) (clockBits := 0)
      (encode (space := space) (clockBits := 0) firstState)).toCfg =
    (decode (tm := tm) (space := space) (clockBits := 0)
      (encode (space := space) (clockBits := 0) secondState)).toCfg at decodeEq
  rw [toCfg_decode_encode firstState firstFits,
    toCfg_decode_encode secondState secondFits] at decodeEq
  exact decodeEq

/-- A terminating run whose every stack fits in `space` has at most one less
step than the number of finite Boolean configuration slices. -/
theorem evalsTo_steps_le_configurationClock
    {first last : tm.Cfg}
    (run : StateTransition.EvalsTo tm.step first (some last))
    (terminal : tm.step last = none)
    (stacksFit : ∀ index : Fin (run.steps + 1), ∀ stack,
      ((PeriodicComputation.stateAt run index).stk stack).length ≤ space) :
    run.steps ≤ 2 ^ configurationBitCount (tm := tm) (space := space) - 1 := by
  let runBits : Fin (run.steps + 1) →
      (Fin (configurationBitCount (tm := tm) (space := space)) → Bool) :=
    fun index => configurationBits (space := space)
      (PeriodicComputation.stateAt run index)
  have runBitsInjective : Function.Injective runBits := by
    intro firstIndex secondIndex bitsEq
    apply PeriodicComputation.stateAt_injective run terminal
    apply configurationBits_injective_of_stacksFit
      (stacksFit firstIndex) (stacksFit secondIndex)
    exact bitsEq
  have cardBound := Fintype.card_le_of_injective runBits runBitsInjective
  simp only [Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool] at cardBound
  have powerPositive :
      0 < 2 ^ configurationBitCount (tm := tm) (space := space) := by
    positivity
  omega

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
