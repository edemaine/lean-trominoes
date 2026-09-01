/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetD

/-! # Elementary semantics of four-column list zipping -/

namespace List

theorem zipWith4_length_of_eq
    {First Second Third Fourth Target : Type*}
    (combine : First → Second → Third → Fourth → Target)
    (first : List First) (second : List Second)
    (third : List Third) (fourth : List Fourth)
    (firstSecond : first.length = second.length)
    (firstThird : first.length = third.length)
    (firstFourth : first.length = fourth.length) :
    (zipWith4 combine first second third fourth).length = first.length := by
  induction first generalizing second third fourth with
  | nil => rfl
  | cons first rest induction =>
      cases second with
      | nil => simp at firstSecond
      | cons second seconds =>
          cases third with
          | nil => simp at firstThird
          | cons third thirds =>
              cases fourth with
              | nil => simp at firstFourth
              | cons fourth fourths =>
                  have secondLength : rest.length = seconds.length := by
                    exact Nat.succ.inj firstSecond
                  have thirdLength : rest.length = thirds.length := by
                    exact Nat.succ.inj firstThird
                  have fourthLength : rest.length = fourths.length := by
                    exact Nat.succ.inj firstFourth
                  change Nat.succ
                      (zipWith4 combine rest seconds thirds fourths).length =
                    Nat.succ rest.length
                  exact congrArg Nat.succ
                    (induction seconds thirds fourths secondLength
                      thirdLength fourthLength)

theorem zipWith4_getD_of_lt
    {First Second Third Fourth Target : Type*}
    (combine : First → Second → Third → Fourth → Target)
    (firstDefault : First) (secondDefault : Second)
    (thirdDefault : Third) (fourthDefault : Fourth)
    (first : List First) (second : List Second)
    (third : List Third) (fourth : List Fourth)
    (firstSecond : first.length = second.length)
    (firstThird : first.length = third.length)
    (firstFourth : first.length = fourth.length)
    (index : Nat) (indexLt : index < first.length) :
    (zipWith4 combine first second third fourth).getD index
        (combine firstDefault secondDefault thirdDefault fourthDefault) =
      combine (first.getD index firstDefault)
        (second.getD index secondDefault)
        (third.getD index thirdDefault)
        (fourth.getD index fourthDefault) := by
  induction first generalizing second third fourth index with
  | nil => simp at indexLt
  | cons first rest induction =>
      cases second with
      | nil => simp at firstSecond
      | cons second seconds =>
          cases third with
          | nil => simp at firstThird
          | cons third thirds =>
              cases fourth with
              | nil => simp at firstFourth
              | cons fourth fourths =>
                  have secondLength : rest.length = seconds.length := by
                    simpa using firstSecond
                  have thirdLength : rest.length = thirds.length := by
                    simpa using firstThird
                  have fourthLength : rest.length = fourths.length := by
                    simpa using firstFourth
                  cases index with
                  | zero => rfl
                  | succ index =>
                      have tailLt : index < rest.length := by
                        simpa using indexLt
                      change
                        (zipWith4 combine rest seconds thirds fourths).getD
                            index
                            (combine firstDefault secondDefault thirdDefault
                              fourthDefault) =
                          combine (rest.getD index firstDefault)
                            (seconds.getD index secondDefault)
                            (thirds.getD index thirdDefault)
                            (fourths.getD index fourthDefault)
                      exact induction seconds thirds fourths secondLength
                        thirdLength fourthLength index tailLt

/-- Four aligned lists can be read as a range map of their total lookups. -/
theorem zipWith4_eq_map_range_getD
    {First Second Third Fourth Target : Type*}
    (combine : First → Second → Third → Fourth → Target)
    (firstDefault : First) (secondDefault : Second)
    (thirdDefault : Third) (fourthDefault : Fourth)
    (first : List First) (second : List Second)
    (third : List Third) (fourth : List Fourth)
    (firstSecond : first.length = second.length)
    (firstThird : first.length = third.length)
    (firstFourth : first.length = fourth.length) :
    zipWith4 combine first second third fourth =
      (List.range first.length).map fun index =>
        combine (first.getD index firstDefault)
          (second.getD index secondDefault)
          (third.getD index thirdDefault)
          (fourth.getD index fourthDefault) := by
  let combined := zipWith4 combine first second third fourth
  have combinedLength : combined.length = first.length :=
    zipWith4_length_of_eq combine first second third fourth
      firstSecond firstThird firstFourth
  calc
    combined = (List.range combined.length).map
        (fun index => combined.getD index
          (combine firstDefault secondDefault thirdDefault fourthDefault)) :=
      (List.map_range_getD combined
        (combine firstDefault secondDefault thirdDefault fourthDefault)).symm
    _ = (List.range first.length).map fun index =>
        combine (first.getD index firstDefault)
          (second.getD index secondDefault)
          (third.getD index thirdDefault)
          (fourth.getD index fourthDefault) := by
      rw [combinedLength]
      apply List.map_congr_left
      intro index indexMember
      exact zipWith4_getD_of_lt combine firstDefault secondDefault
        thirdDefault fourthDefault first second third fourth
        firstSecond firstThird firstFourth index
        (List.mem_range.mp indexMember)

/-- Mapping a four-column result and combining it with a map of the first
column fuses into a single four-column zip. -/
theorem zipWith_map_zipWith4_map_first
    {First Second Third Fourth Middle Tag Target : Type*}
    (select : First → Second → Third → Fourth → Middle)
    (scale : Middle → Middle) (tag : First → Tag)
    (combine : Middle → Tag → Target) :
    ∀ (first : List First) (second : List Second)
      (third : List Third) (fourth : List Fourth),
      List.zipWith combine
          ((zipWith4 select first second third fourth).map scale)
          (first.map tag) =
        zipWith4
          (fun first second third fourth =>
            combine (scale (select first second third fourth)) (tag first))
          first second third fourth
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl
  | _ :: _, _ :: _, _ :: _, [] => rfl
  | first :: firsts, second :: seconds, third :: thirds,
      fourth :: fourths => by
      simp only [zipWith4, List.map_cons, List.zipWith_cons_cons]
      rw [zipWith_map_zipWith4_map_first select scale tag combine
        firsts seconds thirds fourths]

/-- Four-column zipping distributes over aligned prefixes. -/
theorem zipWith4_append_of_prefix_lengths
    {First Second Third Fourth Target : Type*}
    (combine : First → Second → Third → Fourth → Target) :
    ∀ (firstPrefix firstSuffix : List First)
      (secondPrefix secondSuffix : List Second)
      (thirdPrefix thirdSuffix : List Third)
      (fourthPrefix fourthSuffix : List Fourth),
      firstPrefix.length = secondPrefix.length →
      firstPrefix.length = thirdPrefix.length →
      firstPrefix.length = fourthPrefix.length →
      zipWith4 combine
          (firstPrefix ++ firstSuffix)
          (secondPrefix ++ secondSuffix)
          (thirdPrefix ++ thirdSuffix)
          (fourthPrefix ++ fourthSuffix) =
        zipWith4 combine firstPrefix secondPrefix thirdPrefix fourthPrefix ++
          zipWith4 combine firstSuffix secondSuffix thirdSuffix fourthSuffix
  | [], firstSuffix, [], secondSuffix, [], thirdSuffix, [], fourthSuffix,
      _, _, _ => rfl
  | _ :: _, _, [], _, _, _, _, _, firstSecond, _, _ => by
      simp at firstSecond
  | _ :: _, _, _ :: _, _, [], _, _, _, _, firstThird, _ => by
      simp at firstThird
  | _ :: _, _, _ :: _, _, _ :: _, _, [], _, _, _, firstFourth => by
      simp at firstFourth
  | first :: firsts, firstSuffix,
      second :: seconds, secondSuffix,
      third :: thirds, thirdSuffix,
      fourth :: fourths, fourthSuffix,
      firstSecond, firstThird, firstFourth => by
      simp only [List.length_cons] at firstSecond firstThird firstFourth
      simp only [List.cons_append, zipWith4, List.cons_append]
      rw [zipWith4_append_of_prefix_lengths combine
        firsts firstSuffix seconds secondSuffix thirds thirdSuffix
        fourths fourthSuffix (Nat.succ.inj firstSecond)
        (Nat.succ.inj firstThird) (Nat.succ.inj firstFourth)]

/-- Repeating three dynamic values beside a selector list is ordinary
mapping of the corresponding four-argument function. -/
theorem zipWith4_replicate_three
    {Selector First Second Third Target : Type*}
    (combine : Selector → First → Second → Third → Target)
    (selectors : List Selector) (first : First)
    (second : Second) (third : Third) :
    zipWith4 combine selectors
        (List.replicate selectors.length first)
        (List.replicate selectors.length second)
        (List.replicate selectors.length third) =
      selectors.map fun selector => combine selector first second third := by
  induction selectors with
  | nil => rfl
  | cons selector selectors induction =>
      simp only [List.length_cons, List.replicate_succ, zipWith4,
        List.map_cons]
      rw [induction]

end List
