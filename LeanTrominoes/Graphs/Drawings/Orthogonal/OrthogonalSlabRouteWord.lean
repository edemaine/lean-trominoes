/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalSlabRouteComposition

/-! # Simple orthogonal routes assembled from arbitrarily many ordered slabs -/
namespace LeanTrominoes.OrthogonalSlabRouting
open PeriodicOrthocrossing

def SlabRoute.compose (first : SlabRoute) (rest : List SlabRoute) : SlabRoute :=
  rest.foldl SlabRoute.join first

theorem SlabRoute.compose_valid {first : SlabRoute} {rest : List SlabRoute}
    (firstValid : first.IsValid) (restValid : ∀ slab ∈ rest, slab.IsValid)
    (chain : (first :: rest).IsChain (fun first second => first.finish = second.start)) :
    (first.compose rest).IsValid := by
  induction rest generalizing first with
  | nil => exact firstValid
  | cons next tail ih =>
    have nextValid := restValid next (by simp)
    have data := List.isChain_cons_cons.mp chain
    have sameX : first.right = next.left := congrArg Prod.fst data.1
    have sameY : first.target = next.source := congrArg Prod.snd data.1
    have joined := SlabRoute.join_valid firstValid nextValid sameX sameY
    have tailValid : ∀ slab ∈ tail, slab.IsValid := fun slab member => restValid slab (by simp [member])
    have tailChain : (first.join next :: tail).IsChain (fun first second => first.finish = second.start) := by
      cases tail with
      | nil => simp
      | cons after tail =>
        simpa only [List.isChain_cons_cons,SlabRoute.finish,SlabRoute.join] using data.2
    exact ih joined tailValid tailChain

theorem SlabRoute.compose_start (first : SlabRoute) (rest : List SlabRoute) :
    (first.compose rest).start = first.start := by
  induction rest generalizing first with
  | nil => rfl
  | cons next tail ih => exact (ih (first.join next)).trans rfl

theorem SlabRoute.compose_finish (first : SlabRoute) (rest : List SlabRoute) :
    (first.compose rest).finish = (rest.getLast?.getD first).finish := by
  induction rest generalizing first with
  | nil => rfl
  | cons next tail ih =>
    cases tail with
    | nil => rfl
    | cons after tail =>
      have present : (after :: tail).getLast? ≠ none := by simp
      have result := ih (first.join next)
      cases equal : (after :: tail).getLast? with
      | none => exact (present equal).elim
      | some last => simpa only [compose,List.foldl_cons,List.getLast?_cons_cons,equal,Option.getD_some] using result

theorem SlabRoute.compose_head {first : SlabRoute} {rest : List SlabRoute}
    (firstValid : first.IsValid) (restValid : ∀ slab ∈ rest, slab.IsValid)
    (chain : (first :: rest).IsChain (fun first second => first.finish = second.start)) :
    (first.compose rest).points.head? = some first.start := by
  rw [(compose_valid firstValid restValid chain).head,compose_start]

theorem SlabRoute.compose_last {first : SlabRoute} {rest : List SlabRoute}
    (firstValid : first.IsValid) (restValid : ∀ slab ∈ rest, slab.IsValid)
    (chain : (first :: rest).IsChain (fun first second => first.finish = second.start)) :
    (first.compose rest).points.getLast? = some (rest.getLast?.getD first).finish := by
  rw [(compose_valid firstValid restValid chain).last,compose_finish]

theorem SlabRoute.compose_image {first : SlabRoute} {rest : List SlabRoute}
    (firstValid : first.IsValid) (restValid : ∀ slab ∈ rest, slab.IsValid)
    (chain : (first :: rest).IsChain (fun first second => first.finish = second.start)) (point : ℝ × ℝ) :
    GridPolyline.RealContains (first.compose rest).points point ↔
      ∃ slab ∈ first :: rest, GridPolyline.RealContains slab.points point := by
  induction rest generalizing first with
  | nil => simp [compose]
  | cons next tail ih =>
    have nextValid := restValid next (by simp)
    have data := List.isChain_cons_cons.mp chain
    have sameX : first.right = next.left := congrArg Prod.fst data.1
    have sameY : first.target = next.source := congrArg Prod.snd data.1
    have joined := SlabRoute.join_valid firstValid nextValid sameX sameY
    have tailValid : ∀ slab ∈ tail, slab.IsValid := fun slab member => restValid slab (by simp [member])
    have tailChain : (first.join next :: tail).IsChain (fun first second => first.finish = second.start) := by
      cases tail with
      | nil => simp
      | cons after tail => simpa only [List.isChain_cons_cons,SlabRoute.finish,SlabRoute.join] using data.2
    have secondHead : next.points.head? = some first.finish := nextValid.head.trans (congrArg some data.1.symm)
    change GridPolyline.RealContains ((first.join next).compose tail).points point ↔ _
    rw [ih joined tailValid tailChain]
    simp only [List.mem_cons,exists_prop,or_and_right,exists_or,exists_eq_left]
    change (GridPolyline.RealContains (joinPolylines first.points next.points) point ∨ _) ↔ _
    rw [GridPolyline.realContains_join firstValid.last secondHead]
    tauto

end LeanTrominoes.OrthogonalSlabRouting
