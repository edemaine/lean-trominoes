/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealJoinOpenSimple

/-! # A simple orthogonal route assembled from a separated chain of pieces -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

def joinWord : List (List Cell) → List Cell
  | [] => []
  | [first] => first
  | first :: next :: rest => joinPolylines first (joinWord (next :: rest))

def SeparatedWord : List (List Cell) → Prop
  | [] => True
  | [_] => True
  | first :: next :: rest =>
      (∀ point, RealContains first point → RealContains next point →
        point = realCell (first.getLast?.getD (0,0))) ∧
      (∀ later ∈ rest, ∀ point, RealContains first point → RealContains later point → False) ∧
      SeparatedWord (next :: rest)

theorem joinWord_valid {first : List Cell} {rest : List (List Cell)}
    (simple : ∀ piece ∈ first :: rest, IsRealOpenSimple piece)
    (orthogonal : ∀ piece ∈ first :: rest, OrthogonalPolyline piece)
    (chain : (first :: rest).IsChain (fun first next => first.getLast? = next.head?))
    (separated : SeparatedWord (first :: rest)) :
    IsRealOpenSimple (joinWord (first :: rest)) ∧ OrthogonalPolyline (joinWord (first :: rest)) ∧
      (joinWord (first :: rest)).head? = first.head? ∧
      (joinWord (first :: rest)).getLast? = (first :: rest).getLast?.bind List.getLast? ∧
      ∀ point, RealContains (joinWord (first :: rest)) point ↔
        ∃ piece ∈ first :: rest, RealContains piece point := by
  induction rest generalizing first with
  | nil =>
    refine ⟨simple first (by simp),orthogonal first (by simp),rfl,?_,?_⟩
    · simp [joinWord]
    · intro point
      simp [joinWord]
  | cons next rest ih =>
    have firstSimple := simple first (by simp)
    have firstOrthogonal := orthogonal first (by simp)
    have tailSimple : ∀ piece ∈ next :: rest, IsRealOpenSimple piece := fun piece member => simple piece (by simp [member])
    have tailOrthogonal : ∀ piece ∈ next :: rest, OrthogonalPolyline piece := fun piece member => orthogonal piece (by simp [member])
    have chainData := List.isChain_cons_cons.mp chain
    have separation : (∀ point, RealContains first point → RealContains next point →
        point = realCell (first.getLast?.getD (0,0))) ∧
        (∀ later ∈ rest, ∀ point, RealContains first point → RealContains later point → False) ∧
        SeparatedWord (next :: rest) := separated
    have tail := ih tailSimple tailOrthogonal chainData.2 separation.2.2
    have nonempty : first ≠ [] := by
      intro empty
      have long := firstSimple.1
      simp [empty] at long
    have lastPresent : first.getLast? ≠ none := by simpa using nonempty
    cases firstLast : first.getLast? with
    | none => exact (lastPresent firstLast).elim
    | some joint =>
      have tailHead : (joinWord (next :: rest)).head? = some joint :=
        tail.2.2.1.trans (chainData.1.symm.trans firstLast)
      have contacts : ∀ point, RealContains first point → RealContains (joinWord (next :: rest)) point →
          point = realCell joint := by
        intro point firstContains tailContains
        obtain ⟨piece,member,pieceContains⟩ := (tail.2.2.2.2 point).mp tailContains
        rcases List.mem_cons.mp member with rfl | member
        · simpa only [firstLast,Option.getD_some] using separation.1 point firstContains pieceContains
        · exact (separation.2.1 piece member point firstContains pieceContains).elim
      change IsRealOpenSimple (joinPolylines first (joinWord (next :: rest))) ∧ _
      refine ⟨isRealOpenSimple_join firstSimple tail.1 firstLast tailHead contacts,?_,?_,?_,?_⟩
      · exact isChain_joinPolylines firstOrthogonal tail.2.1 (firstLast.trans tailHead.symm)
      · exact joinPolylines_head?_of_first nonempty
      · change (joinPolylines first (joinWord (next :: rest))).getLast? = _
        rw [joinPolylines_getLast?_of_second tail.1.1,tail.2.2.2.1,List.getLast?_cons_cons]
      · intro point
        change RealContains (joinPolylines first (joinWord (next :: rest))) point ↔ _
        rw [realContains_join firstLast tailHead,tail.2.2.2.2]
        simp only [List.mem_cons,exists_prop,or_and_right,exists_or,exists_eq_left]

theorem joinWord_isRealOpenSimple {first : List Cell} {rest : List (List Cell)}
    (simple : ∀ piece ∈ first :: rest, IsRealOpenSimple piece)
    (orthogonal : ∀ piece ∈ first :: rest, OrthogonalPolyline piece)
    (chain : (first :: rest).IsChain (fun first next => first.getLast? = next.head?))
    (separated : SeparatedWord (first :: rest)) : IsRealOpenSimple (joinWord (first :: rest)) :=
  (joinWord_valid simple orthogonal chain separated).1

theorem joinWord_orthogonal {first : List Cell} {rest : List (List Cell)}
    (simple : ∀ piece ∈ first :: rest, IsRealOpenSimple piece)
    (orthogonal : ∀ piece ∈ first :: rest, OrthogonalPolyline piece)
    (chain : (first :: rest).IsChain (fun first next => first.getLast? = next.head?))
    (separated : SeparatedWord (first :: rest)) : OrthogonalPolyline (joinWord (first :: rest)) :=
  (joinWord_valid simple orthogonal chain separated).2.1

end LeanTrominoes.GridPolyline
