/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRestoreSteps

/-! # Restoring the finite tag stream for source cycle-link emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def restoreTags_evalsInTime (tag : Tag) (values : List Tag)
    (data : TapeData) (reverseEq : data.tagReverse = values) :
    EvalsToInTime machine.step (restoreTagsCfg tag data)
      (some (restoreTargetsCfg tag
        { data with
          tagReverse := []
          tags := values.reverse ++ data.tags }))
      (2 * values.length + 1) := by
  induction values generalizing data with
  | nil =>
      have step := step_restoreTags_nil tag data reverseEq
      simpa using oneStep step
  | cons current values induction =>
      let afterPop : TapeData := { data with tagReverse := values }
      let nextData : TapeData :=
        { afterPop with tags := current :: data.tags }
      let popped := oneStep
        (step_restoreTags_cons tag current data values reverseEq)
      let pushed := oneStep
        (step_pushTagForward tag current afterPop)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * values.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, afterPop, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
