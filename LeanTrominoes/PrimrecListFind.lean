/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Computability.Primrec.List

/-! # Primitive-recursive parameterized list search -/

noncomputable section

namespace Primrec

/-- First-match search is primitive recursive when both the input list and
the input-dependent Boolean predicate are primitive recursive. -/
theorem list_find?
    {Alpha Beta : Type*}
    [Primcodable Alpha] [Primcodable Beta]
    {values : Alpha → List Beta}
    {predicate : Alpha → Beta → Bool}
    (valuesPrimrec : Primrec values)
    (predicatePrimrec : Primrec₂ predicate) :
    Primrec fun input => (values input).find? (predicate input) := by
  have step : Primrec₂ fun
      (input : Alpha) (state : Beta × List Beta × Option Beta) =>
        bif predicate input state.1 then
          some state.1
        else
          state.2.2 := by
    have condition : Primrec fun data :
        Alpha × (Beta × List Beta × Option Beta) =>
      predicate data.1 data.2.1 :=
      predicatePrimrec.comp Primrec.fst
        (Primrec.fst.comp Primrec.snd)
    exact (Primrec.cond condition
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  have correct (input : Alpha) : ∀ entries : List Beta,
      List.recOn entries none (fun head tail previous =>
        bif predicate input head then some head else previous) =
        entries.find? (predicate input) := by
    intro entries
    induction entries with
    | nil => rfl
    | cons head tail induction =>
        by_cases selected : predicate input head = true
        · simp [List.find?, selected]
        · simp [List.find?, selected, induction]
  exact (Primrec.list_rec valuesPrimrec
    (Primrec.const none) step).of_eq fun input =>
      correct input (values input)

end Primrec
