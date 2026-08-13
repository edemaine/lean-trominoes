/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineDesignatedFormula

/-!
# Semantic PSPACE reduction to local 1D periodic CNF

For a certified polynomial-space decider and one input, this file chooses the
certified space bound, counts bounded Boolean configuration slices to obtain a
clock width, and compiles the initial configuration together with the unique
terminal encoding of `true`.  The resulting local 1D periodic CNF belongs to
the source language exactly when the original input belongs to the language.

The remaining hardness work is quantitative: certify that this function on
encoded inputs is polynomial-time and then transport it through the geometric
reductions.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

namespace PolySpaceReduction

variable {Input : Type} {encoding : Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

def initialConfiguration (input : Input) : decider.tm.Cfg :=
  initList decider.tm
    (List.map decider.inputAlphabet.invFun (encoding.encode input))

/-- Exact accepting endpoint: the decider's canonical encoded `true` output. -/
def acceptingConfiguration : decider.tm.Cfg :=
  haltList decider.tm
    (List.map decider.outputAlphabet.invFun
      ((Complexity.primcodableFinEncoding Bool).encode true))

/-- Width budget used by the generated formula.  Besides the certified
reachable-space polynomial, it explicitly reserves the exact initial and
designated `true` endpoint sizes so both fixed configurations always fit. -/
def reductionSpace (input : Input) : Nat :=
  decider.space.eval (encoding.encode input).length +
    Complexity.configurationSpace decider.tm
      (initialConfiguration decider input) +
    Complexity.configurationSpace decider.tm
      (acceptingConfiguration decider)

/-- The finite configuration-code width is also a sufficient reset-clock bit
width: a terminating deterministic run cannot repeat a bounded slice. -/
def reductionClockBits (input : Input) : Nat :=
  BoundedMachineAtom.configurationBitCount (tm := decider.tm)
    (space := reductionSpace decider input)

/-- The semantic many-one reduction before its polynomial-time certificate. -/
def formula (input : Input) : PeriodicCNF Nat :=
  BoundedMachineAtom.designatedMachinePeriodicCNF
    (tm := decider.tm) (space := reductionSpace decider input)
    (clockBits := reductionClockBits decider input)
    (initialConfiguration decider input)
    (acceptingConfiguration decider)

private theorem initialStacksFit (input : Input) (stack : decider.tm.K) :
    ((initialConfiguration decider input).stk stack).length ≤
      reductionSpace decider input := by
  apply (PeriodicComputation.stack_length_le_configurationSpace decider.tm
    (initialConfiguration decider input) stack).trans
  unfold reductionSpace
  omega

private theorem acceptingStacksFit (input : Input)
    (stack : decider.tm.K) :
    ((acceptingConfiguration decider).stk stack).length ≤
      reductionSpace decider input := by
  apply (PeriodicComputation.stack_length_le_configurationSpace decider.tm
    (acceptingConfiguration decider) stack).trans
  simp [reductionSpace]

private theorem runStackFits (input : Input)
    {terminal : decider.tm.Cfg}
    (run : StateTransition.EvalsTo decider.tm.step
      (initialConfiguration decider input) (some terminal))
    (index : Fin (run.steps + 1)) (stack : decider.tm.K) :
    ((PeriodicComputation.stateAt run index).stk stack).length ≤
      reductionSpace decider input := by
  apply (PeriodicComputation.stack_length_le_configurationSpace
    decider.tm (PeriodicComputation.stateAt run index) stack).trans
  apply (decider.space_le input (PeriodicComputation.stateAt run index)
    (PeriodicComputation.stateAt_reaches run index)).trans
  unfold reductionSpace
  omega

private theorem acceptingStepNone :
    decider.tm.step (acceptingConfiguration decider) = none := by
  rfl

/-- Semantic correctness of the compiled polynomial-space machine history. -/
theorem mem_iff_localPeriodicCNF1DSAT (input : Input) :
    language input ↔ LocalPeriodicCNF1DSAT (formula decider input) := by
  constructor
  · intro member
    have resultTrue : decider.result input = true :=
      (decider.correct input).mpr member
    let run : StateTransition.EvalsTo decider.tm.step
        (initialConfiguration decider input)
        (some (acceptingConfiguration decider)) := by
      simpa [TM2Outputs, initialConfiguration, acceptingConfiguration,
        resultTrue] using decider.outputs input
    have runFits := runStackFits decider input run
    have lengthBound : run.steps ≤
        2 ^ reductionClockBits decider input - 1 := by
      apply BoundedMachineAtom.evalsTo_steps_le_configurationClock
        (space := reductionSpace decider input) run
        (acceptingStepNone decider)
      exact runFits
    let trace : PeriodicComputation.AcceptingTrace decider.tm.Cfg
        (initialConfiguration decider input) decider.tm.step
        (BoundedMachineAtom.designatedMachineAccepts
          (acceptingConfiguration decider))
        (2 ^ reductionClockBits decider input - 1) :=
      { length := run.steps
        length_le := lengthBound
        states := PeriodicComputation.stateAt run
        starts := PeriodicComputation.stateAt_zero run
        accepts_last := by
          simp [BoundedMachineAtom.designatedMachineAccepts,
            PeriodicComputation.stateAt_last]
        not_accepts := by
          intro index accepted
          have step := PeriodicComputation.stateAt_step run index
          rw [show PeriodicComputation.stateAt run index.castSucc =
              acceptingConfiguration decider from accepted,
            acceptingStepNone decider] at step
          cases step
        steps := PeriodicComputation.stateAt_step run }
    refine ⟨
      BoundedMachineAtom.designatedMachinePeriodicCNF_oneDimensional
        (initialConfiguration decider input) (acceptingConfiguration decider),
      BoundedMachineAtom.designatedMachinePeriodicCNF_localOnLine
        (initialConfiguration decider input) (acceptingConfiguration decider),
      ?_⟩
    apply BoundedMachineAtom.designatedMachinePeriodicCNF_satisfiableOnLine_of_acceptingTrace
        (initialConfiguration decider input) (acceptingConfiguration decider)
        trace
    exact runFits
  · intro holds
    have initialFits := initialStacksFit decider input
    have acceptingFits := acceptingStacksFit decider input
    obtain ⟨trace⟩ := BoundedMachineAtom.acceptingTrace_of_designatedMachinePeriodicCNF_satisfiableOnLine
        (initialConfiguration decider input) (acceptingConfiguration decider)
        initialFits acceptingFits holds.2.2
    have acceptingReachable : StateTransition.Reaches decider.tm.step
        (initialConfiguration decider input)
        (acceptingConfiguration decider) := by
      have reachesLast := trace.reaches (Fin.last trace.length)
      have lastEq : trace.states (Fin.last trace.length) =
          acceptingConfiguration decider := trace.accepts_last
      rwa [lastEq] at reachesLast
    let actualTerminal : decider.tm.Cfg :=
      haltList decider.tm
        (List.map decider.outputAlphabet.invFun
          ((Complexity.primcodableFinEncoding Bool).encode
            (decider.result input)))
    let outputRun : StateTransition.EvalsTo decider.tm.step
        (initialConfiguration decider input) (some actualTerminal) := by
      simpa [TM2Outputs, initialConfiguration, actualTerminal] using
        decider.outputs input
    have actualReachable : StateTransition.Reaches decider.tm.step
        (initialConfiguration decider input) actualTerminal :=
      PeriodicComputation.evalsTo_reaches outputRun
    have terminalsEq : actualTerminal = acceptingConfiguration decider :=
      PeriodicComputation.eq_of_reachable_terminals actualReachable
        acceptingReachable (by rfl) (acceptingStepNone decider)
    have stackEq := congrArg
      (fun configuration : decider.tm.Cfg => configuration.stk decider.tm.k₁)
      terminalsEq
    have encodedEq :
        (Complexity.primcodableFinEncoding Bool).encode
            (decider.result input) =
          (Complexity.primcodableFinEncoding Bool).encode true := by
      have mappedEq :
          List.map decider.outputAlphabet.invFun
              ((Complexity.primcodableFinEncoding Bool).encode
                (decider.result input)) =
            List.map decider.outputAlphabet.invFun
              ((Complexity.primcodableFinEncoding Bool).encode true) := by
        simpa [actualTerminal, acceptingConfiguration, haltList] using stackEq
      exact (List.map_injective_iff.mpr
        decider.outputAlphabet.symm.injective) mappedEq
    have resultTrue : decider.result input = true :=
      Computability.Encoding.encode_injective
        (Complexity.primcodableFinEncoding Bool).toEncoding encodedEq
    exact (decider.correct input).mp resultTrue

end PolySpaceReduction

end PeriodicCNF

end LeanTrominoes
