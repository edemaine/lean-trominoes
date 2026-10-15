/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

/-! # Pointwise addition of three aligned natural-number columns -/

namespace LeanTrominoes.AlignedThreeNatColumns

/-- Mapping three aligned columns and adding their values is the same as
zipping the source columns and then mapping the combined value. -/
theorem zip_map_add
    {First Second Third : Type}
    (firstValue : First → Nat)
    (secondValue : Second → Nat)
    (thirdValue : Third → Nat)
    (firsts : List First) (seconds : List Second) (thirds : List Third)
    (secondLength : seconds.length = firsts.length)
    (thirdLength : thirds.length = firsts.length) :
    List.zipWith (fun first second => first + second)
        (List.zipWith (fun first third => first + third)
          (firsts.map firstValue) (thirds.map thirdValue))
        (seconds.map secondValue) =
      (List.zip firsts (List.zip seconds thirds)).map fun aligned =>
        firstValue aligned.1 + thirdValue aligned.2.2 +
          secondValue aligned.2.1 := by
  induction firsts generalizing seconds thirds with
  | nil =>
      cases seconds with
      | cons second seconds => simp at secondLength
      | nil =>
          cases thirds with
          | cons third thirds => simp at thirdLength
          | nil => rfl
  | cons first firsts induction =>
      cases seconds with
      | nil => simp at secondLength
      | cons second seconds =>
          cases thirds with
          | nil => simp at thirdLength
          | cons third thirds =>
              have secondTailLength : seconds.length = firsts.length := by
                simpa using secondLength
              have thirdTailLength : thirds.length = firsts.length := by
                simpa using thirdLength
              simp only [List.map_cons, List.zipWith_cons_cons,
                List.zip_cons_cons]
              rw [induction seconds thirds secondTailLength thirdTailLength]

end LeanTrominoes.AlignedThreeNatColumns
