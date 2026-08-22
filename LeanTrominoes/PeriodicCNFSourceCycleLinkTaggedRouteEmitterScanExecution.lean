/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterLinkSteps
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterScanExecutionData

/-! # Complete tagged cycle-link scan execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def scanLinks_evalsInTime
    (input : SourceCycleLinkTaggedRouteEmitter.Input) (cursor : Tag)
    (linkIndex : Nat) (tags : List Tag) (targets : List Nat)
    (outputReverse output : List OutputToken)
    (lengthEq : tags.length = targets.length) :
    EvalsToInTime machine.step
      (scanLinksCfg cursor
        (scanTapeData input linkIndex tags targets outputReverse output))
      (some (reverseOutputCfg (finalTag cursor tags)
        (scanTapeData input (linkIndex + tags.length) [] []
          ((SourceCycleLinkTaggedRouteEmitter.emitAux
            input linkIndex tags targets).reverse ++ outputReverse)
          output)))
      (scanTime input linkIndex tags targets outputReverse output) := by
  induction tags generalizing cursor linkIndex targets outputReverse with
  | nil =>
      have targetsNil : targets = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst targets
      have step := oneStep
        (step_scanLinks_nil cursor
          (scanTapeData input linkIndex [] [] outputReverse output) rfl)
      simpa [scanTapeData, finalTag, scanTime,
        SourceCycleLinkTaggedRouteEmitter.emitAux] using step
  | cons tag tags induction =>
      cases targets with
      | nil => simp at lengthEq
      | cons target targets =>
          have tailLength : tags.length = targets.length := by
            simpa using lengthEq
          let startData := scanTapeData input linkIndex
            (tag :: tags) (target :: targets) outputReverse output
          let afterPop := scanTapeData input linkIndex
            tags (target :: targets) outputReverse output
          let nextOutput :=
            (SourceCycleLinkTaggedRouteEmitter.linkTokens
              input linkIndex target tag).reverse ++ outputReverse
          let nextData := scanTapeData input (linkIndex + 1)
            tags targets nextOutput output
          have popped := oneStep
            (step_scanLinks_cons cursor tag startData tags rfl)
          have targetEq : afterPop.targets =
              List.replicate target .unit ++ .delimiter ::
                UnaryFieldEncoderMachine.unaryFields targets := by
            exact scanTapeData_target_cons input linkIndex target tags targets
              outputReverse output
          have linkRun := link_evalsInTime tag afterPop target
            (UnaryFieldEncoderMachine.unaryFields targets) targetEq rfl
          have nextDataEq :
              afterLinkData afterPop target
                  (UnaryFieldEncoderMachine.unaryFields targets) tag =
                nextData := by
            simpa only [afterPop, nextData, nextOutput] using
              (afterLinkData_scanTapeData_eq input linkIndex target tag tags
                targets outputReverse output)
          have linkRun' : EvalsToInTime machine.step
              (beginSourceRecordCfg tag afterPop)
              (some (scanLinksCfg tag nextData))
              (linkTime afterPop target
                (UnaryFieldEncoderMachine.unaryFields targets) tag) := by
            rw [nextDataEq] at linkRun
            exact linkRun
          have firstLink := EvalsToInTime.trans machine.step
            1 (linkTime afterPop target
              (UnaryFieldEncoderMachine.unaryFields targets) tag)
            _ _ _ popped linkRun'
          have rest := induction tag (linkIndex + 1) targets
            nextOutput tailLength
          have whole := EvalsToInTime.trans machine.step
            (linkTime afterPop target
                (UnaryFieldEncoderMachine.unaryFields targets) tag + 1)
            (scanTime input (linkIndex + 1) tags targets nextOutput output)
            _ _ _ firstLink rest
          convert whole using 1 <;>
            simp [afterPop, nextOutput, scanTime,
              finalTag, SourceCycleLinkTaggedRouteEmitter.emitAux,
              List.reverse_append, List.append_assoc, List.length_cons,
              tailLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
