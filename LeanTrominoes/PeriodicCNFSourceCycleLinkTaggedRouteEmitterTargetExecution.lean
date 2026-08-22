/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetSteps

/-! # Unary target-field execution for tagged cycle-link route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem replicate_atomUnit_cons_comm (count : Nat)
    (tail : List OutputToken) :
    List.replicate count (.atomUnit : OutputToken) ++ .atomUnit :: tail =
      .atomUnit :: (List.replicate count (.atomUnit : OutputToken) ++ tail) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append, induction]

noncomputable def scanTarget_evalsInTime (count : Nat) (tag : Tag)
    (data : TapeData) (remaining : List UnarySymbol)
    (targetsEq : data.targets =
      List.replicate count .unit ++ .delimiter :: remaining) :
    EvalsToInTime machine.step
      (scanTargetCfg tag data)
      (some (finishSourceTargetCfg tag
        { data with
          targets := remaining
          outputReverse :=
            List.replicate count .atomUnit ++ data.outputReverse }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := oneStep
        (step_scanTarget_delimiter tag data remaining targetsEq)
      simpa using step
  | succ count induction =>
      have sourceEq : data.targets =
          .unit :: (List.replicate count .unit ++
            .delimiter :: remaining) := by
        simpa only [List.replicate_succ, List.cons_append] using targetsEq
      let nextData : TapeData :=
        { data with
          targets := List.replicate count .unit ++ .delimiter :: remaining
          outputReverse := .atomUnit :: data.outputReverse }
      have first := oneStep
        (step_scanTarget_unit tag data
          (List.replicate count .unit ++ .delimiter :: remaining) sourceEq)
      have nextTargetsEq : nextData.targets =
          List.replicate count .unit ++ .delimiter :: remaining := by
        rfl
      have rest := induction nextData nextTargetsEq
      have composed := EvalsToInTime.trans machine.step
        1 (count + 1)
        (scanTargetCfg tag data)
        (scanTargetCfg tag nextData)
        (some (finishSourceTargetCfg tag
          { nextData with
            targets := remaining
            outputReverse :=
              List.replicate count .atomUnit ++ nextData.outputReverse }))
        first rest
      simpa only [nextData, List.length_replicate, List.replicate_succ,
        List.cons_append, replicate_atomUnit_cons_comm, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using composed

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
