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

/-- Right-to-left loop erasure always returns a duplicate-free list. -/
theorem listLoopErase_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (points : List Vertex) :
    (listLoopErase points).Nodup := by
  induction points with
  | nil => simp [listLoopErase]
  | cons head tail induction =>
      simp only [listLoopErase]
      by_cases member : head ∈ listLoopErase tail
      · rw [if_pos member]
        exact List.Pairwise.drop induction
      · rw [if_neg member]
        exact List.nodup_cons.mpr ⟨member, induction⟩

/-- Applying right-to-left loop erasure twice has no further effect. -/
@[simp] theorem listLoopErase_idempotent
    {Vertex : Type*} [DecidableEq Vertex]
    (points : List Vertex) :
    listLoopErase (listLoopErase points) =
      listLoopErase points :=
  listLoopErase_eq_self_of_nodup (listLoopErase_nodup points)

/-- A suffix may be loop-erased before processing any prefix.  This is the
unconditional localization law supplied by the algorithm's right-to-left
recursion. -/
theorem listLoopErase_append_right
    {Vertex : Type*} [DecidableEq Vertex]
    (first second : List Vertex) :
    listLoopErase (first ++ second) =
      listLoopErase (first ++ listLoopErase second) := by
  induction first with
  | nil =>
      simp
  | cons head tail induction =>
      simp only [List.cons_append, listLoopErase]
      rw [induction]

/-- A correctly matched endpoint join is the first route without its final
copy of the boundary followed by the complete second route. -/
theorem joinAtEndpoint_eq_dropLast_append
    {Vertex : Type*}
    {first second : List Vertex}
    {boundary : Vertex}
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary) :
    joinAtEndpoint first second = first.dropLast ++ second := by
  unfold joinAtEndpoint
  rw [← List.dropLast_append_getLast? boundary firstLast]
  cases second with
  | nil => simp at secondHead
  | cons head tail =>
      have headEq : head = boundary := by
        simpa using secondHead
      subst head
      simp

/-- In an endpoint join, the complete right route may be loop-erased before
the combined route is processed. -/
theorem listLoopErase_joinAtEndpoint_right
    {Vertex : Type*} [DecidableEq Vertex]
    {first second : List Vertex}
    {boundary : Vertex}
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary)
    (erasedSecondHead :
      (listLoopErase second).head? = some boundary) :
    listLoopErase (joinAtEndpoint first second) =
      listLoopErase
        (joinAtEndpoint first (listLoopErase second)) := by
  rw [joinAtEndpoint_eq_dropLast_append firstLast secondHead,
    joinAtEndpoint_eq_dropLast_append firstLast erasedSecondHead]
  exact listLoopErase_append_right first.dropLast second

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

/-- If two point lists meet only at their advertised join boundary, loop
erasure can be performed on the first list alone and then rejoined to the
duplicate-free second list. -/
theorem listLoopErase_joinAtEndpoint_of_only_common
    {Vertex : Type*} [DecidableEq Vertex]
    (first second : List Vertex)
    (boundary : Vertex)
    (secondHead : second.head? = some boundary)
    (secondNodup : second.Nodup)
    (onlyCommon :
      ∀ point, point ∈ first → point ∈ second →
        point = boundary) :
    listLoopErase (joinAtEndpoint first second) =
      joinAtEndpoint (listLoopErase first) second := by
  have disjointTail : List.Disjoint first second.tail := by
    rw [List.disjoint_left]
    intro point firstMember secondTailMember
    have pointEq := onlyCommon point firstMember
      (List.mem_of_mem_tail secondTailMember)
    subst point
    cases second with
    | nil => simp at secondHead
    | cons head tail =>
        have headEq : head = boundary := by
          simpa using secondHead
        subst head
        exact (List.nodup_cons.mp secondNodup).1 secondTailMember
  unfold joinAtEndpoint
  exact listLoopErase_append_of_disjoint
    first second.tail disjointTail secondNodup.tail

end Computability
end LeanTrominoes
