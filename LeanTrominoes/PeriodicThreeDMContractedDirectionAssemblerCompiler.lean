/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerMachine

/-! # Polynomial-time role-tagged contracted direction assembly -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace ContractedDirectionAssembler

open Computability StateTransition Turing
open NormalizationDirectionRequest.Batch

private def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration}
    (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

theorem directionBlock_length_le_one (token : Token) :
    (directionBlock token).length ≤ 1 := by
  cases token <;> simp [directionBlock]

theorem directions_length_le (tokens : List Token) :
    (directions tokens).length ≤ tokens.length := by
  induction tokens with
  | nil => simp [directions]
  | cons token tokens induction =>
      simp only [directions, List.flatMap_cons, List.length_append,
        List.length_cons]
      change (directionBlock token).length +
        (directions tokens).length ≤ tokens.length + 1
      have tokenBound := directionBlock_length_le_one token
      omega

def forward_evalsInTime (input : List Token)
    (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    EvalsToInTime (TM2.step program)
      (forwardCfg input forwardReverse output)
      (some (drainCfg
        ((directions input).reverse ++ forwardReverse) output))
      (input.length + 1) := by
  induction input generalizing forwardReverse with
  | nil =>
      simpa [directions] using
        oneStep (step_forward_nil forwardReverse output)
  | cons token input induction =>
      have first := oneStep
        (step_forward_cons token input forwardReverse output)
      have rest := induction
        ((directionBlock token).reverse ++ forwardReverse)
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (input.length + 1)
        (forwardCfg (token :: input) forwardReverse output)
        (forwardCfg input
          ((directionBlock token).reverse ++ forwardReverse) output)
        (some (drainCfg
          ((directions (token :: input)).reverse ++ forwardReverse)
          output)) first (by
            simpa [directions, List.reverse_append,
              List.append_assoc] using rest)
      simpa [Nat.add_assoc] using composed

def drain_evalsInTime (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    EvalsToInTime (TM2.step program)
      (drainCfg forwardReverse output)
      (some (haltCfg
        (forwardReverse.reverse.map .direction ++ output)))
      (forwardReverse.length + 1) := by
  induction forwardReverse generalizing output with
  | nil =>
      simpa using oneStep (step_drain_nil output)
  | cons direction forwardReverse induction =>
      have first := oneStep
        (step_drain_cons direction forwardReverse output)
      have rest := induction (.direction direction :: output)
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (forwardReverse.length + 1)
        (drainCfg (direction :: forwardReverse) output)
        (drainCfg forwardReverse (.direction direction :: output))
        (some (haltCfg
          ((direction :: forwardReverse).reverse.map .direction ++
            output))) first (by
              simpa [List.reverse_cons, List.map_append,
                List.append_assoc] using rest)
      simpa [Nat.add_assoc] using composed

def forwardAndDrain_evalsInTime (input : List Token)
    (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    EvalsToInTime (TM2.step program)
      (forwardCfg input forwardReverse output)
      (some (haltCfg
        ((forwardReverse.reverse ++ directions input).map
          .direction ++ output)))
      (input.length + (directions input).length +
        forwardReverse.length + 2) := by
  have scanned := forward_evalsInTime input forwardReverse output
  have drained := drain_evalsInTime
    ((directions input).reverse ++ forwardReverse) output
  have composed := EvalsToInTime.trans (TM2.step program)
    (input.length + 1)
    (((directions input).reverse ++ forwardReverse).length + 1)
    (forwardCfg input forwardReverse output)
    (drainCfg ((directions input).reverse ++ forwardReverse) output)
    (some (haltCfg
      ((forwardReverse.reverse ++ directions input).map .direction ++
        output))) scanned (by
          simpa [List.reverse_append, List.map_append,
            List.append_assoc] using drained)
  convert composed using 1 <;>
    simp [List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] <;> omega

def reverse_evalsInTime (input : List Token)
    (output : List NormalizedToken) :
    EvalsToInTime (TM2.step program)
      (reverseCfg input output)
      (some (haltCfg
        ((Gadget.reverseDirections (directions input)).map
          .direction ++ output)))
      (input.length + 1) := by
  induction input generalizing output with
  | nil =>
      simpa [directions, Gadget.reverseDirections] using
        oneStep (step_reverse_nil output)
  | cons token input induction =>
      let emitted :=
        (Gadget.reverseDirections (directionBlock token)).map
          NormalizedToken.direction ++ output
      have first := oneStep (step_reverse_cons token input output)
      have rest := induction emitted
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (input.length + 1)
        (reverseCfg (token :: input) output)
        (reverseCfg input emitted)
        (some (haltCfg
          ((Gadget.reverseDirections
            (directions (token :: input))).map .direction ++ output)))
        (by simpa [emitted] using first) (by
          simpa [directions, emitted, Gadget.reverseDirections_append,
            List.map_append, List.append_assoc] using rest)
      simpa [Nat.add_assoc] using composed

def initializeForward_evalsInTime
    (terminal : Bool) (first : Option AxisDirection)
    (state : State) (input : List Token) :
    EvalsToInTime (TM2.step program)
      (initializeForwardCfg terminal first state input)
      (some (haltCfg
        ((first.toList ++ directions input).map .direction ++
          if terminal then [.routeEnd] else [])))
      (input.length + (directions input).length +
        first.toList.length + 3) := by
  have initialized := oneStep
    (step_initializeForward terminal first state input)
  have rest := forwardAndDrain_evalsInTime input first.toList
    (if terminal then [.routeEnd] else [])
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (input.length + (directions input).length +
      first.toList.length + 2)
    (initializeForwardCfg terminal first state input)
    (forwardCfg input first.toList
      (if terminal then [.routeEnd] else []))
    (some (haltCfg
      ((first.toList ++ directions input).map .direction ++
        if terminal then [.routeEnd] else []))) initialized (by
          cases first <;> simpa using rest)
  convert composed using 1 <;> omega

def initializeReverse_evalsInTime (state : State)
    (input : List Token) :
    EvalsToInTime (TM2.step program)
      (initializeReverseCfg state input)
      (some (haltCfg
        ((Gadget.reverseDirections (directions input)).map
          .direction ++ [.routeEnd])))
      (input.length + 2) := by
  have initialized := oneStep (step_initializeReverse state input)
  have rest := reverse_evalsInTime input [.routeEnd]
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (input.length + 1)
    (initializeReverseCfg state input)
    (reverseCfg input [.routeEnd])
    (some (haltCfg
      ((Gadget.reverseDirections (directions input)).map
        .direction ++ [.routeEnd]))) initialized rest
  convert composed using 1 <;> omega

def start_evalsInTime (input : List Token) :
    EvalsToInTime (TM2.step program)
      (startCfg input)
      (some (haltCfg (blockOutput input)))
      (2 * input.length + 4) := by
  cases input with
  | nil =>
      have first := oneStep step_start_nil
      have rest := initializeForward_evalsInTime true none none []
      have composed := EvalsToInTime.trans (TM2.step program)
        1 3 (startCfg [])
        (initializeForwardCfg true none none [])
        (some (haltCfg (blockOutput []))) first (by
          simpa [blockOutput, selectedRole, directions, directionBlock,
            NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock]
            using rest)
      simpa using composed
  | cons token input =>
      have first := oneStep (step_start_cons token input)
      cases token with
      | role role =>
          cases role with
          | retained =>
              have rest := initializeForward_evalsInTime true none
                (some (.inl (.role .retained))) input
              have composed := EvalsToInTime.trans (TM2.step program)
                1 (input.length + (directions input).length + 3)
                (startCfg (.role .retained :: input))
                (initializeForwardCfg true none
                  (some (.inl (.role .retained))) input)
                (some (haltCfg (blockOutput (.role .retained :: input))))
                first (by
                  simpa [blockOutput, selectedRole, directions, directionBlock,
                    NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock]
                    using rest)
              exact
                { toEvalsTo := composed.toEvalsTo
                  steps_le_m := composed.steps_le_m.trans (by
                    simp only [List.length_cons]
                    have bound := directions_length_le input
                    omega) }
          | throughFirst =>
              have rest := initializeForward_evalsInTime false none
                (some (.inl (.role .throughFirst))) input
              have composed := EvalsToInTime.trans (TM2.step program)
                1 (input.length + (directions input).length + 3)
                (startCfg (.role .throughFirst :: input))
                (initializeForwardCfg false none
                  (some (.inl (.role .throughFirst))) input)
                (some (haltCfg
                  (blockOutput (.role .throughFirst :: input)))) first (by
                    simpa [blockOutput, selectedRole, directions,
                      directionBlock] using rest)
              exact
                { toEvalsTo := composed.toEvalsTo
                  steps_le_m := composed.steps_le_m.trans (by
                    simp only [List.length_cons]
                    have bound := directions_length_le input
                    omega) }
          | throughSecond =>
              have rest := initializeReverse_evalsInTime
                (some (.inl (.role .throughSecond))) input
              have composed := EvalsToInTime.trans (TM2.step program)
                1 (input.length + 2)
                (startCfg (.role .throughSecond :: input))
                (initializeReverseCfg
                  (some (.inl (.role .throughSecond))) input)
                (some (haltCfg
                  (blockOutput (.role .throughSecond :: input)))) first (by
                    simpa [blockOutput, selectedRole, directions,
                      directionBlock,
                      NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock]
                      using rest)
              exact
                { toEvalsTo := composed.toEvalsTo
                  steps_le_m := composed.steps_le_m.trans (by
                    simp only [List.length_cons]
                    omega) }
      | direction direction =>
          have rest := initializeForward_evalsInTime true (some direction)
            (some (.inl (.direction direction))) input
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (input.length + (directions input).length + 4)
            (startCfg (.direction direction :: input))
            (initializeForwardCfg true (some direction)
              (some (.inl (.direction direction))) input)
            (some (haltCfg
              (blockOutput (.direction direction :: input)))) first (by
                simpa [blockOutput, selectedRole, directions, directionBlock,
                  NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock]
                  using rest)
          exact
            { toEvalsTo := composed.toEvalsTo
              steps_le_m := composed.steps_le_m.trans (by
                simp only [List.length_cons]
                have bound := directions_length_le input
                omega) }
      | incidenceEnd =>
          have rest := initializeForward_evalsInTime true none
            (some (.inl .incidenceEnd)) input
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (input.length + (directions input).length + 3)
            (startCfg (.incidenceEnd :: input))
            (initializeForwardCfg true none
              (some (.inl .incidenceEnd)) input)
            (some (haltCfg (blockOutput (.incidenceEnd :: input)))) first (by
              simpa [blockOutput, selectedRole, directions, directionBlock,
                NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock]
                using rest)
          exact
            { toEvalsTo := composed.toEvalsTo
              steps_le_m := composed.steps_le_m.trans (by
                simp only [List.length_cons]
                have bound := directions_length_le input
                omega) }

theorem initList_eq_startCfg (input : List Token) :
    initList machine input = startCfg input := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk (some Label.start) none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

theorem haltList_eq_haltCfg (output : List NormalizedToken) :
    haltList machine output = haltCfg output := by
  apply congrArg (fun stackValues => TM2.Cfg.mk none none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

def outputsInTime (input : List Token) :
    TM2OutputsInTime machine input (some (blockOutput input))
      (2 * input.length + 4) := by
  change EvalsToInTime (TM2.step program)
    (initList machine input)
    (some (haltList machine (blockOutput input)))
    (2 * input.length + 4)
  rw [initList_eq_startCfg input, haltList_eq_haltCfg]
  exact start_evalsInTime input

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 4

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 2 * length + 4 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- One role-tagged incidence word is assembled in linear time. -/
noncomputable def blockOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id blockOutput where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    simpa only [id_eq, FiniteBlockTransducer.map_refl_invFun,
      timePolynomial_eval] using outputsInTime input

end ContractedDirectionAssembler
end PeriodicThreeDM
end LeanTrominoes

end
