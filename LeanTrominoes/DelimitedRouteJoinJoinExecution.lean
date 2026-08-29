/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinExecutionSupport
import LeanTrominoes.DelimitedRouteJoinJoinSteps

/-! # Complete prefix/suffix joining execution -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open StateTransition Turing

def phaseCfg : Phase → TapeData → machine.Cfg
  | .prefix => scanPrefixCfg
  | .suffix => scanSuffixCfg

def joinTime : Phase → List Token → List Token → Nat
  | .prefix, [], _ => 1
  | .prefix, .direction _ :: prefixes, suffixes =>
      2 + joinTime .prefix prefixes suffixes
  | .prefix, .routeEnd :: prefixes, suffixes =>
      1 + joinTime .suffix prefixes suffixes
  | .suffix, _, [] => 1
  | .suffix, prefixes, .direction _ :: suffixes =>
      2 + joinTime .suffix prefixes suffixes
  | .suffix, prefixes, .routeEnd :: suffixes =>
      2 + joinTime .prefix prefixes suffixes
  termination_by _phase prefixes suffixes =>
    prefixes.length + suffixes.length
  decreasing_by
    all_goals simp_wf

def joining_evalsInTime
    (phase : Phase) (prefixes suffixes : List Token)
    (data : TapeData)
    (prefixEq : data.prefixes = prefixes)
    (suffixEq : data.suffixes = suffixes) :
    let result := resultAux phase prefixes suffixes
    EvalsToInTime machine.step (phaseCfg phase data)
      (some (cleanupPrefixesCfg
        { data with
          prefixes := result.remainingPrefixes
          suffixes := result.remainingSuffixes
          outputReverse := result.output.reverse ++ data.outputReverse }))
      (joinTime phase prefixes suffixes) := by
  cases phase with
  | «prefix» =>
      cases prefixes with
      | nil =>
          have step := oneStep (step_scanPrefix_nil data prefixEq)
          simpa [phaseCfg, resultAux, joinTime, prefixEq, suffixEq] using step
      | cons token prefixes =>
          cases token with
          | direction direction =>
              let afterPop : TapeData :=
                { data with prefixes := prefixes }
              let afterPush : TapeData :=
                { afterPop with outputReverse :=
                    (.direction direction : Token) ::
                      afterPop.outputReverse }
              have popped := oneStep
                (step_scanPrefix_direction data direction prefixes prefixEq)
              have pushed := oneStep
                (step_pushPrefixToken afterPop direction)
              have rest := joining_evalsInTime Phase.prefix prefixes suffixes
                afterPush rfl (by simpa [afterPush, afterPop] using suffixEq)
              have firstTwo := EvalsToInTime.trans machine.step
                1 1 _ _ _ popped pushed
              have whole := EvalsToInTime.trans machine.step
                2 (joinTime Phase.prefix prefixes suffixes)
                _ _ _ firstTwo rest
              simpa [phaseCfg, resultAux, joinTime, afterPop, afterPush,
                List.reverse_cons, List.append_assoc, Nat.add_assoc,
                Nat.add_comm]
                using whole
          | routeEnd =>
              let afterPop : TapeData :=
                { data with prefixes := prefixes }
              have popped := oneStep
                (step_scanPrefix_routeEnd data prefixes prefixEq)
              have rest := joining_evalsInTime Phase.suffix prefixes suffixes
                afterPop rfl (by simpa [afterPop] using suffixEq)
              have whole := EvalsToInTime.trans machine.step
                1 (joinTime Phase.suffix prefixes suffixes)
                _ _ _ popped rest
              simpa [phaseCfg, resultAux, joinTime, afterPop,
                Nat.add_assoc, Nat.add_comm] using whole
  | suffix =>
      cases suffixes with
      | nil =>
          have step := oneStep (step_scanSuffix_nil data suffixEq)
          simpa [phaseCfg, resultAux, joinTime, prefixEq, suffixEq] using step
      | cons token suffixes =>
          cases token with
          | direction direction =>
              let afterPop : TapeData :=
                { data with suffixes := suffixes }
              let afterPush : TapeData :=
                { afterPop with outputReverse :=
                    (.direction direction : Token) ::
                      afterPop.outputReverse }
              have popped := oneStep
                (step_scanSuffix_cons data (.direction direction)
                  suffixes suffixEq)
              have pushed := oneStep
                (step_pushSuffixToken_direction afterPop direction)
              have rest := joining_evalsInTime Phase.suffix prefixes suffixes
                afterPush (by simpa [afterPush, afterPop] using prefixEq) rfl
              have firstTwo := EvalsToInTime.trans machine.step
                1 1 _ _ _ popped pushed
              have whole := EvalsToInTime.trans machine.step
                2 (joinTime Phase.suffix prefixes suffixes)
                _ _ _ firstTwo rest
              simpa [phaseCfg, resultAux, joinTime, afterPop, afterPush,
                List.reverse_cons, List.append_assoc, Nat.add_assoc,
                Nat.add_comm]
                using whole
          | routeEnd =>
              let afterPop : TapeData :=
                { data with suffixes := suffixes }
              let afterPush : TapeData :=
                { afterPop with outputReverse :=
                    (.routeEnd : Token) :: afterPop.outputReverse }
              have popped := oneStep
                (step_scanSuffix_cons data .routeEnd suffixes suffixEq)
              have pushed := oneStep
                (step_pushSuffixToken_routeEnd afterPop)
              have rest := joining_evalsInTime Phase.prefix prefixes suffixes
                afterPush (by simpa [afterPush, afterPop] using prefixEq) rfl
              have firstTwo := EvalsToInTime.trans machine.step
                1 1 _ _ _ popped pushed
              have whole := EvalsToInTime.trans machine.step
                2 (joinTime Phase.prefix prefixes suffixes)
                _ _ _ firstTwo rest
              simpa [phaseCfg, resultAux, joinTime, afterPop, afterPush,
                List.reverse_cons, List.append_assoc, Nat.add_assoc,
                Nat.add_comm]
                using whole
  termination_by prefixes.length + suffixes.length
  decreasing_by
    all_goals simp_all

end LeanTrominoes.DelimitedRouteJoin

end
