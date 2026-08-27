/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureComputability

/-!
# Loop erasure across a disjoint suffix

The proof-free right-to-left loop eraser commutes with appending a
duplicate-free suffix when the two input point lists are disjoint.  This is
the list-level localization principle needed to isolate the finite loops in
Figure 9 from the inherited source-route tail.
-/

namespace LeanTrominoes
namespace Computability

/-- Loop erasure changes nothing on an already duplicate-free list. -/
theorem listLoopErase_eq_self_of_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    {points : List Vertex}
    (nodup : points.Nodup) :
    listLoopErase points = points := by
  induction points with
  | nil => rfl
  | cons head tail induction =>
      have headFresh : head ∉ tail := (List.nodup_cons.mp nodup).1
      have tailNodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      simp [listLoopErase, induction tailNodup, headFresh]

/-- A disjoint duplicate-free suffix passes through right-to-left loop
erasure unchanged. -/
theorem listLoopErase_append_of_disjoint
    {Vertex : Type*} [DecidableEq Vertex]
    (first second : List Vertex)
    (disjoint : List.Disjoint first second)
    (secondNodup : second.Nodup) :
    listLoopErase (first ++ second) =
      listLoopErase first ++ second := by
  induction first with
  | nil =>
      simpa [listLoopErase] using
        listLoopErase_eq_self_of_nodup secondNodup
  | cons head tail induction =>
      have contact := List.disjoint_cons_left.mp disjoint
      simp only [List.cons_append, listLoopErase,
        induction contact.2]
      by_cases member : head ∈ listLoopErase tail
      · have appendedMember :
            head ∈ listLoopErase tail ++ second := by
          simp [member]
        rw [if_pos member, if_pos appendedMember,
          List.idxOf_append_of_mem member,
          List.drop_append_of_le_length
            (Nat.le_of_lt (List.idxOf_lt_length_of_mem member))]
      · have appendedNotMember :
            head ∉ listLoopErase tail ++ second := by
          simp [member, contact.1]
        rw [if_neg member, if_neg appendedNotMember]
        simp

end Computability
end LeanTrominoes
