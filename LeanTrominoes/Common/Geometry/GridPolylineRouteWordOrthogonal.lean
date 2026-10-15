/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRouteWordEndpoints

/-! # Orthogonality and exact image of any connected word of nontrivial routes -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem joinWord_orthogonal_image {first : List Cell} {rest : List (List Cell)}
    (long : ∀ piece ∈ first :: rest, 2 ≤ piece.length)
    (orthogonal : ∀ piece ∈ first :: rest, OrthogonalPolyline piece)
    (chain : (first :: rest).IsChain (fun first next => first.getLast? = next.head?)) :
    OrthogonalPolyline (joinWord (first :: rest)) ∧
      ∀ point, RealContains (joinWord (first :: rest)) point ↔
        ∃ piece ∈ first :: rest, RealContains piece point := by
  induction rest generalizing first with
  | nil =>
    refine ⟨orthogonal first (by simp),?_⟩
    intro point
    simp [joinWord]
  | cons next rest ih =>
    have tailLong : ∀ piece ∈ next :: rest, 2 ≤ piece.length := fun piece member => long piece (by simp [member])
    have tailOrthogonal : ∀ piece ∈ next :: rest, OrthogonalPolyline piece := fun piece member => orthogonal piece (by simp [member])
    have chainData := List.isChain_cons_cons.mp chain
    have tail := ih tailLong tailOrthogonal chainData.2
    have tailEndpoints := joinWord_endpoints tailLong
    have nonempty : first ≠ [] := by
      intro empty
      have firstLong := long first (by simp)
      simp [empty] at firstLong
    have lastPresent : first.getLast? ≠ none := by simpa using nonempty
    cases firstLast : first.getLast? with
    | none => exact (lastPresent firstLast).elim
    | some joint =>
      have tailHead : (joinWord (next :: rest)).head? = some joint :=
        tailEndpoints.2.1.trans (chainData.1.symm.trans firstLast)
      change OrthogonalPolyline (joinPolylines first (joinWord (next :: rest))) ∧ _
      refine ⟨isChain_joinPolylines (orthogonal first (by simp)) tail.1 (firstLast.trans tailHead.symm),?_⟩
      intro point
      change RealContains (joinPolylines first (joinWord (next :: rest))) point ↔ _
      rw [realContains_join firstLast tailHead,tail.2]
      simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]

end LeanTrominoes.GridPolyline
