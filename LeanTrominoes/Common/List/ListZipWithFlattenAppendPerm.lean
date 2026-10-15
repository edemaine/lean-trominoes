/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Zip

/-! # Separating appended blocks in a two-list zip -/

namespace List

/-- Flattening blocks that are pointwise appends is a permutation of all
first components followed by all second components. -/
theorem zipWith_flatten_append_perm
    {First Second Element : Type*}
    (left right : First → Second → List Element) :
    ∀ (firsts : List First) (seconds : List Second),
    (List.zipWith
      (fun first second => left first second ++ right first second)
      firsts seconds).flatten.Perm
      ((List.zipWith left firsts seconds).flatten ++
        (List.zipWith right firsts seconds).flatten)
  | [], _ => List.Perm.nil
  | _ :: _, [] => List.Perm.nil
  | first :: firsts, second :: seconds => by
      simp only [List.zipWith, List.flatten_cons]
      let leftHead := left first second
      let rightHead := right first second
      let leftTail := (List.zipWith left firsts seconds).flatten
      let rightTail := (List.zipWith right firsts seconds).flatten
      have tail := zipWith_flatten_append_perm left right firsts seconds
      have firstPerm :
          ((leftHead ++ rightHead) ++
              (List.zipWith
                (fun first second =>
                  left first second ++ right first second)
                firsts seconds).flatten).Perm
            ((leftHead ++ rightHead) ++ (leftTail ++ rightTail)) :=
        List.Perm.append_left _ tail
      have swapPerm :
          ((leftHead ++ rightHead) ++ (leftTail ++ rightTail)).Perm
            ((leftHead ++ leftTail) ++ (rightHead ++ rightTail)) := by
        have comm : (rightHead ++ leftTail).Perm
            (leftTail ++ rightHead) :=
          List.perm_append_comm
        simpa only [List.append_assoc] using
          (comm.append_right rightTail).append_left leftHead
      exact firstPerm.trans swapPerm

/-- The analogous separation of three pointwise-appended components. -/
theorem zipWith_flatten_append3_perm
    {First Second Element : Type*}
    (first middle last : First → Second → List Element)
    (firsts : List First) (seconds : List Second) :
    (List.zipWith
      (fun one two => first one two ++ middle one two ++ last one two)
      firsts seconds).flatten.Perm
      ((List.zipWith first firsts seconds).flatten ++
        (List.zipWith middle firsts seconds).flatten ++
        (List.zipWith last firsts seconds).flatten) := by
  simpa only [List.append_assoc] using
    (zipWith_flatten_append_perm first
      (fun one two => middle one two ++ last one two)
      firsts seconds).trans
    (List.Perm.append (List.Perm.refl _)
      (zipWith_flatten_append_perm middle last firsts seconds))

end List
