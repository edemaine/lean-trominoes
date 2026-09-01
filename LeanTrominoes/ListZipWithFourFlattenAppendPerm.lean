/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Zip

/-! # Separating appended blocks in a four-list zip -/

namespace List

/-- Flattening blocks that are pointwise appends is a permutation of all
first components followed by all second components. -/
theorem zipWith4_flatten_append_perm
    {First Second Third Fourth Element : Type*}
    (left right : First → Second → Third → Fourth → List Element)
    (firsts : List First) (seconds : List Second)
    (thirds : List Third) (fourths : List Fourth) :
    (List.zipWith4
      (fun first second third fourth =>
        left first second third fourth ++
          right first second third fourth)
      firsts seconds thirds fourths).flatten.Perm
      ((List.zipWith4 left firsts seconds thirds fourths).flatten ++
        (List.zipWith4 right firsts seconds thirds fourths).flatten) := by
  induction firsts generalizing seconds thirds fourths with
  | nil => exact List.Perm.nil
  | cons first firsts induction =>
      cases seconds with
      | nil => exact List.Perm.nil
      | cons second seconds =>
          cases thirds with
          | nil => exact List.Perm.nil
          | cons third thirds =>
              cases fourths with
              | nil => exact List.Perm.nil
              | cons fourth fourths =>
                  simp only [List.zipWith4, List.flatten_cons]
                  let leftHead := left first second third fourth
                  let rightHead := right first second third fourth
                  let leftTail :=
                    (List.zipWith4 left firsts seconds thirds fourths).flatten
                  let rightTail :=
                    (List.zipWith4 right firsts seconds thirds fourths).flatten
                  have tail := induction seconds thirds fourths
                  have firstPerm :
                      ((leftHead ++ rightHead) ++
                          (List.zipWith4
                            (fun first second third fourth =>
                              left first second third fourth ++
                                right first second third fourth)
                            firsts seconds thirds fourths).flatten).Perm
                        ((leftHead ++ rightHead) ++
                          (leftTail ++ rightTail)) :=
                    List.Perm.append_left _ tail
                  have swapPerm :
                      ((leftHead ++ rightHead) ++
                          (leftTail ++ rightTail)).Perm
                        ((leftHead ++ leftTail) ++
                          (rightHead ++ rightTail)) := by
                    have comm :
                        (rightHead ++ leftTail).Perm
                          (leftTail ++ rightHead) :=
                      List.perm_append_comm
                    simpa only [List.append_assoc] using
                      (comm.append_right rightTail).append_left leftHead
                  exact firstPerm.trans swapPerm

end List
