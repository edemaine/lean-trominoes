/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterHeaderLoopExecution

/-! # Complete header parsing for tagged source cycle-link route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def scanHeader_evalsInTime (tag : Tag) (clauseTotal : Nat)
    (values : List Tag) (tail : List InputSymbol) (data : TapeData)
    (inputEq : data.input =
      List.replicate clauseTotal (.left (.left .unit)) ++
        .left (.left .delimiter) :: .left .separator ::
          values.map (fun value => .left (.right value)) ++
            .separator :: tail) :
    EvalsToInTime machine.step (scanHeaderCfg tag data)
      (some (scanTargetsInputCfg tag
        { data with
          input := tail
          tagReverse := values.reverse ++ data.tagReverse
          clauseCount :=
            List.replicate clauseTotal () ++ data.clauseCount
          literalCount :=
            List.replicate values.length () ++ data.literalCount }))
      (2 * clauseTotal + 2 * values.length + 3) := by
  let tagInput : List InputSymbol :=
    values.map (fun value => .left (.right value)) ++ .separator :: tail
  let innerTail : List InputSymbol := .left .separator :: tagInput
  let clauseTail : List InputSymbol :=
    .left (.left .delimiter) :: innerTail
  let afterUnits : TapeData :=
    { data with
      input := clauseTail
      clauseCount := List.replicate clauseTotal () ++ data.clauseCount }
  let afterDelimiter : TapeData := { afterUnits with input := innerTail }
  let afterInner : TapeData := { afterDelimiter with input := tagInput }
  let afterTags : TapeData :=
    { afterInner with
      input := .separator :: tail
      tagReverse := values.reverse ++ data.tagReverse
      literalCount :=
        List.replicate values.length () ++ data.literalCount }
  let units := scanClauseUnits_evalsInTime tag clauseTotal clauseTail data
    (by simpa [clauseTail, innerTail, tagInput, List.append_assoc] using inputEq)
  let delimiter := oneStep
    (step_scanHeader_clauseDelimiter tag afterUnits innerTail rfl)
  let innerSeparator := oneStep
    (step_scanHeader_innerSeparator tag afterDelimiter tagInput rfl)
  let tags := scanTags_evalsInTime tag values (.separator :: tail)
    afterInner rfl
  let outerSeparator := oneStep
    (step_scanHeader_outerSeparator tag afterTags tail rfl)
  let throughDelimiter := EvalsToInTime.trans machine.step
    (2 * clauseTotal) 1 _ _ _ units delimiter
  let throughInner := EvalsToInTime.trans machine.step
    (1 + 2 * clauseTotal) 1 _ _ _ throughDelimiter innerSeparator
  let throughTags := EvalsToInTime.trans machine.step
    (1 + (1 + 2 * clauseTotal)) (2 * values.length)
      _ _ _ throughInner tags
  let whole := EvalsToInTime.trans machine.step
    (2 * values.length + (1 + (1 + 2 * clauseTotal))) 1
      _ _ _ throughTags outerSeparator
  have timeEq :
      1 + (2 * values.length + (1 + (1 + 2 * clauseTotal))) =
        2 * clauseTotal + 2 * values.length + 3 := by
    omega
  rw [← timeEq]
  simpa [whole, throughTags, throughInner, throughDelimiter, afterTags,
    afterInner, afterDelimiter, afterUnits, clauseTail, innerTail, tagInput,
    Nat.add_assoc] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
