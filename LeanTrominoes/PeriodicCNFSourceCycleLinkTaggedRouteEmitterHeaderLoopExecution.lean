/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterHeaderSteps

/-! # Header parsing loops for tagged source cycle-link route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

@[simp] private theorem replicate_unit_succ_append (count : Nat)
    (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      List.replicate (count + 1) () ++ tail := by
  calc
    List.replicate count () ++ () :: tail =
        (List.replicate count () ++ List.replicate 1 ()) ++ tail := by
      simp [List.append_assoc]
    _ = List.replicate (count + 1) () ++ tail := by
      rw [List.replicate_add]

def scanClauseUnits_evalsInTime (tag : Tag) (count : Nat)
    (tail : List InputSymbol) (data : TapeData)
    (inputEq : data.input =
      List.replicate count (.left (.left .unit)) ++ tail) :
    EvalsToInTime machine.step (scanHeaderCfg tag data)
      (some (scanHeaderCfg tag
        { data with
          input := tail
          clauseCount :=
            List.replicate count () ++ data.clauseCount }))
      (2 * count) := by
  induction count generalizing data with
  | zero =>
      rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
        clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
      change input = tail at inputEq
      subst input
      simpa using (EvalsToInTime.refl machine.step
        (scanHeaderCfg tag
          ⟨tail, tagReverse, tags, targetReverse, targets, clauseCount,
            literalCount, linkIndex, scratch, outputReverse, output⟩))
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append] at inputEq
      let afterPop : TapeData :=
        { data with
          input := List.replicate count (.left (.left .unit)) ++ tail }
      let nextData : TapeData :=
        { afterPop with clauseCount := () :: data.clauseCount }
      let popped := oneStep
        (step_scanHeader_clauseUnit tag data _ inputEq)
      let pushed := oneStep (step_pushClauseUnit tag afterPop)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * count) _ _ _ firstTwo rest
      simpa [whole, nextData, afterPop, Nat.mul_add, Nat.add_assoc] using whole

def scanTags_evalsInTime (tag : Tag) (values : List Tag)
    (tail : List InputSymbol) (data : TapeData)
    (inputEq : data.input =
      values.map (fun value => .left (.right value)) ++ tail) :
    EvalsToInTime machine.step (scanHeaderCfg tag data)
      (some (scanHeaderCfg tag
        { data with
          input := tail
          tagReverse := values.reverse ++ data.tagReverse
          literalCount :=
            List.replicate values.length () ++ data.literalCount }))
      (2 * values.length) := by
  induction values generalizing data with
  | nil =>
      rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
        clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
      change input = tail at inputEq
      subst input
      simpa using (EvalsToInTime.refl machine.step
        (scanHeaderCfg tag
          ⟨tail, tagReverse, tags, targetReverse, targets, clauseCount,
            literalCount, linkIndex, scratch, outputReverse, output⟩))
  | cons current values induction =>
      have inputHead : data.input =
          .left (.right current) ::
            (values.map (fun value => .left (.right value)) ++ tail) := by
        simpa [List.map_cons] using inputEq
      let afterPop : TapeData :=
        { data with
          input := values.map (fun value => .left (.right value)) ++ tail }
      let nextData : TapeData :=
        { afterPop with
          tagReverse := current :: data.tagReverse
          literalCount := () :: data.literalCount }
      let popped := oneStep
        (step_scanHeader_tag tag current data _ inputHead)
      let pushed := oneStep (step_pushTagReverse tag current afterPop)
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * values.length) _ _ _ firstTwo rest
      simpa [whole, nextData, afterPop, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
