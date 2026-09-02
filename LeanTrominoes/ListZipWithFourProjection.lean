/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Zip

/-! # Elementary projections of three- and four-list zips -/

namespace List

/-- Flattening singleton blocks produced by a four-list zip removes the
singleton wrapper. -/
theorem zipWith4_flatten_singleton
    {First Second Third Fourth Target : Type*}
    (combine : First → Second → Third → Fourth → Target) :
    ∀ (firsts : List First) (seconds : List Second)
      (thirds : List Third) (fourths : List Fourth),
      (zipWith4 (fun first second third fourth =>
        [combine first second third fourth])
        firsts seconds thirds fourths).flatten =
      zipWith4 combine firsts seconds thirds fourths
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl
  | _ :: _, _ :: _, _ :: _, [] => rfl
  | first :: firsts, second :: seconds, third :: thirds,
      fourth :: fourths => by
      simp only [zipWith4, List.flatten_cons, List.cons_append,
        List.nil_append]
      rw [zipWith4_flatten_singleton combine
        firsts seconds thirds fourths]

/-- A four-list zip whose result ignores the fourth column is the
corresponding three-list zip when that column is long enough. -/
theorem zipWith4_ignore_fourth_of_length_eq
    {First Second Third Fourth Target : Type*}
    (combine : First → Second → Third → Target) :
    ∀ (firsts : List First) (seconds : List Second)
      (thirds : List Third) (fourths : List Fourth),
      firsts.length = fourths.length →
      zipWith4 (fun first second third _ => combine first second third)
          firsts seconds thirds fourths =
        zipWith3 combine firsts seconds thirds
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, lengthEq => by simp at lengthEq
  | _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], lengthEq => by simp at lengthEq
  | first :: firsts, second :: seconds, third :: thirds,
      fourth :: fourths, lengthEq => by
      simp only [List.length_cons] at lengthEq
      simp only [zipWith4, zipWith3]
      rw [zipWith4_ignore_fourth_of_length_eq combine
        firsts seconds thirds fourths (Nat.succ.inj lengthEq)]

/-- Mapping the result of a three-list zip fuses into its combining
function. -/
theorem map_zipWith3
    {First Second Third Middle Target : Type*}
    (transform : Middle → Target)
    (combine : First → Second → Third → Middle) :
    ∀ (firsts : List First) (seconds : List Second) (thirds : List Third),
      (zipWith3 combine firsts seconds thirds).map transform =
        zipWith3 (fun first second third =>
          transform (combine first second third)) firsts seconds thirds
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | first :: firsts, second :: seconds, third :: thirds => by
      simp only [zipWith3, List.map_cons]
      rw [map_zipWith3 transform combine firsts seconds thirds]

/-- Projecting the second of four equally long columns is ordinary mapping
of that column. -/
theorem zipWith4_project_second_of_lengths
    {First Second Third Fourth Target : Type*}
    (project : Second → Target) :
    ∀ (firsts : List First) (seconds : List Second)
      (thirds : List Third) (fourths : List Fourth),
      firsts.length = seconds.length →
      firsts.length = thirds.length →
      firsts.length = fourths.length →
      zipWith4 (fun _ second _ _ => project second)
          firsts seconds thirds fourths =
        seconds.map project
  | [], [], [], [], _, _, _ => rfl
  | [], _ :: _, _, _, firstSecond, _, _ => by simp at firstSecond
  | [], [], _ :: _, _, _, firstThird, _ => by simp at firstThird
  | [], [], [], _ :: _, _, _, firstFourth => by simp at firstFourth
  | _ :: _, [], _, _, firstSecond, _, _ => by simp at firstSecond
  | _ :: _, _ :: _, [], _, _, firstThird, _ => by simp at firstThird
  | _ :: _, _ :: _, _ :: _, [], _, _, firstFourth => by simp at firstFourth
  | first :: firsts, second :: seconds, third :: thirds,
      fourth :: fourths, firstSecond, firstThird, firstFourth => by
      simp only [List.length_cons] at firstSecond firstThird firstFourth
      simp only [zipWith4, List.map_cons]
      rw [zipWith4_project_second_of_lengths project
        firsts seconds thirds fourths
        (Nat.succ.inj firstSecond) (Nat.succ.inj firstThird)
        (Nat.succ.inj firstFourth)]

end List
