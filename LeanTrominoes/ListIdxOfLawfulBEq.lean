/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Independence of `List.idxOf` from lawful Boolean equality -/

namespace LeanTrominoes

/-- Any two lawful Boolean equality implementations compute the same list
index. -/
theorem listIdxOf_eq_of_lawfulBEq
    {Element : Type*}
    (first second : BEq Element)
    (firstLawful : @LawfulBEq Element first)
    (secondLawful : @LawfulBEq Element second)
    (item : Element) (items : List Element) :
    @List.idxOf Element first item items =
      @List.idxOf Element second item items := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      have testEq : @BEq.beq Element first head item =
          @BEq.beq Element second head item := by
        apply Bool.eq_iff_iff.mpr
        simp only [@beq_iff_eq Element first firstLawful,
          @beq_iff_eq Element second secondLawful]
      simp only [List.idxOf_cons, testEq, induction]

end LeanTrominoes
