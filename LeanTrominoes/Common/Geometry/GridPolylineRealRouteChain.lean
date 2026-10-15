/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealJoinSimple
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineJoin

/-! # Joining a finite chain of open simple routes -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

def joinRouteChain : List (List Cell) → List Cell
  | [] => []
  | [route] => route
  | first::second::rest => joinPolylines first (joinRouteChain (second::rest))

theorem joinRouteChain_head {first : List Cell} (rest : List (List Cell)) (nonempty : first≠[]) :
    (joinRouteChain (first::rest)).head?=first.head? := by
  cases rest with
  | nil => rfl
  | cons second rest =>
      cases first with
      | nil => exact (nonempty rfl).elim
      | cons point tail => rfl

theorem joinRouteChain_long {first : List Cell} (rest : List (List Cell)) (long : 2≤first.length) :
    2≤(joinRouteChain (first::rest)).length := by
  cases rest with
  | nil => exact long
  | cons second rest =>
      simp only [joinRouteChain,joinPolylines,List.length_append,List.length_tail]
      omega

theorem joinRouteChain_last {routes : List (List Cell)}
    (long : ∀ route∈routes, 2≤route.length) :
    (joinRouteChain routes).getLast?=routes.getLast?.bind List.getLast? := by
  induction routes using List.twoStepInduction with
  | nil => rfl
  | singleton route => simp only [joinRouteChain,List.getLast?_singleton,Option.bind_some]
  | cons_cons first second rest _ induction =>
      rw [joinRouteChain,joinPolylines_getLast?_of_second (joinRouteChain_long rest (long second (by simp)))]
      simpa only [List.getLast?_cons_cons] using induction second
        (fun route member => long route (List.mem_cons_of_mem first member))

theorem joinRouteChain_map (transform : Cell → Cell) (routes : List (List Cell)) :
    joinRouteChain (routes.map (List.map transform))=(joinRouteChain routes).map transform := by
  induction routes using List.twoStepInduction with
  | nil => rfl
  | singleton route => rfl
  | cons_cons first second rest _ induction =>
      simpa only [List.map_cons,joinRouteChain,joinPolylines,List.map_append,List.map_tail] using
        congrArg (fun tail => first.map transform ++ tail.tail) (induction second)

theorem joinRouteChain_orthogonal {routes : List (List Cell)}
    (chain : routes.IsChain (fun first second => first.getLast?=second.head?))
    (long : ∀ route∈routes, 2≤route.length)
    (orthogonal : ∀ route∈routes, OrthogonalPolyline route) :
    OrthogonalPolyline (joinRouteChain routes) := by
  induction routes using List.twoStepInduction with
  | nil => simp [joinRouteChain,OrthogonalPolyline]
  | singleton route => exact orthogonal route (by simp)
  | cons_cons first second rest _ induction =>
      have chainParts := List.isChain_cons_cons.mp chain
      have secondLong := long second (by simp)
      have secondNonempty : second≠[] := by intro empty; simp only [empty,List.length_nil] at secondLong; omega
      obtain ⟨joint,secondHead⟩ : ∃ joint,second.head?=some joint := by
        cases second with
        | nil => exact (secondNonempty rfl).elim
        | cons point tail => exact ⟨point,rfl⟩
      have firstLast := chainParts.1.trans secondHead
      have tailHead := (joinRouteChain_head rest secondNonempty).trans secondHead
      exact (orthogonal first (by simp)).joinAtEndpoint
        (induction second chainParts.2 (fun route member => long route (List.mem_cons_of_mem first member))
          (fun route member => orthogonal route (List.mem_cons_of_mem first member))) firstLast tailHead

theorem joinRouteChain_contains {routes : List (List Cell)}
    (chain : routes.IsChain (fun first second => first.getLast?=second.head?))
    (long : ∀ route∈routes, 2≤route.length) {p : ℝ × ℝ}
    (contains : RealContains (joinRouteChain routes) p) :
    ∃ route∈routes, RealContains route p := by
  induction routes using List.twoStepInduction with
  | nil => simp only [joinRouteChain,RealContains,gridPolylineSegments,List.not_mem_nil,false_and,exists_false] at contains
  | singleton route => exact ⟨route,by simp,contains⟩
  | cons_cons first second rest _ induction =>
      have chainParts := List.isChain_cons_cons.mp chain
      have secondLong := long second (by simp)
      have secondNonempty : second≠[] := by intro empty; simp only [empty,List.length_nil] at secondLong; omega
      obtain ⟨joint,secondHead⟩ : ∃ joint,second.head?=some joint := by
        cases second with
        | nil => exact (secondNonempty rfl).elim
        | cons point tail => exact ⟨point,rfl⟩
      have firstLast := chainParts.1.trans secondHead
      have tailHead := (joinRouteChain_head rest secondNonempty).trans secondHead
      rw [joinRouteChain,realContains_join firstLast tailHead] at contains
      rcases contains with firstContains | tailContains
      · exact ⟨first,by simp,firstContains⟩
      · obtain ⟨route,member,routeContains⟩ := induction second chainParts.2
          (fun route member => long route (List.mem_cons_of_mem first member)) tailContains
        exact ⟨route,List.mem_cons_of_mem first member,routeContains⟩

def MeetsAtLast (first second : List Cell) : Prop :=
  ∀ p, RealContains first p → RealContains second p →
    ∀ last, first.getLast?=some last → p=realCell last

theorem joinRouteChain_openSimple {routes : List (List Cell)} (nonempty : routes≠[])
    (simple : ∀ route∈routes, IsRealOpenSimple route)
    (chain : routes.IsChain (fun first second => first.getLast?=second.head?))
    (contacts : routes.Pairwise MeetsAtLast) : IsRealOpenSimple (joinRouteChain routes) := by
  induction routes using List.twoStepInduction with
  | nil => exact (nonempty rfl).elim
  | singleton route => exact simple route (by simp)
  | cons_cons first second rest _ induction =>
      have chainParts := List.isChain_cons_cons.mp chain
      have contactParts := List.pairwise_cons.mp contacts
      have tailSimple := induction second (by simp)
        (fun route member => simple route (List.mem_cons_of_mem first member)) chainParts.2 contactParts.2
      have secondLong := (simple second (by simp)).1
      have secondNonempty : second≠[] := by intro empty; simp only [empty,List.length_nil] at secondLong; omega
      obtain ⟨joint,secondHead⟩ : ∃ joint,second.head?=some joint := by
        cases second with
        | nil => exact (secondNonempty rfl).elim
        | cons point tail => exact ⟨point,rfl⟩
      have firstLast := chainParts.1.trans secondHead
      have tailHead := (joinRouteChain_head rest secondNonempty).trans secondHead
      apply isRealOpenSimple_join (simple first (by simp)) tailSimple firstLast tailHead
      intro p firstContains tailContains
      obtain ⟨route,member,routeContains⟩ := joinRouteChain_contains chainParts.2
        (fun route member => (simple route (List.mem_cons_of_mem first member)).1) tailContains
      exact contactParts.1 route member p firstContains routeContains joint firstLast

end LeanTrominoes.GridPolyline
