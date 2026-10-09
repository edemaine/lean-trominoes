/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealRouteChain

/-! # Simple finite route chains with an optional closing contact -/
namespace LeanTrominoes.GridPolyline

def RouteContactPattern (routes : List (List Cell)) : Prop :=
  ∀ i j (hi : i < routes.length) (hj : j < routes.length), i < j →
    ∀ p, RealContains routes[i] p → RealContains routes[j] p →
      (∃ joint, routes[i].getLast?=some joint ∧ p=realCell joint) ∨
      (i=0 ∧ j+1=routes.length ∧ ∃ outer,
        routes[i].head?=some outer ∧ routes[j].getLast?=some outer ∧ p=realCell outer)

theorem joinRouteChain_simple {routes : List (List Cell)} (nonempty : routes≠[])
    (simple : ∀ route∈routes, IsRealOpenSimple route)
    (chain : routes.IsChain (fun first second => first.getLast?=second.head?))
    (contacts : RouteContactPattern routes) : IsRealSimple (joinRouteChain routes) := by
  cases routes with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil => exact (simple first (by simp)).isRealSimple
      | cons second rest =>
          have chainParts := List.isChain_cons_cons.mp chain
          have tailContacts : (second::rest).Pairwise MeetsAtLast := by
            apply List.pairwise_iff_getElem.mpr
            intro i j hi hj ordered p firstContains secondContains last firstLast
            have contact := contacts (i+1) (j+1) (Nat.succ_lt_succ hi)
              (Nat.succ_lt_succ hj) (by omega) p firstContains secondContains
            rcases contact with ⟨joint,atLast,equal⟩ | closed
            · exact equal.trans (congrArg realCell (Option.some.inj (atLast.symm.trans firstLast)))
            · omega
          have tailSimple := joinRouteChain_openSimple (by simp)
            (fun route member => simple route (List.mem_cons_of_mem first member)) chainParts.2 tailContacts
          have firstSimple := simple first (by simp)
          have firstLong := firstSimple.1
          have secondLong := (simple second (by simp)).1
          have firstNonempty : first≠[] := by intro empty; simp only [empty,List.length_nil] at firstLong; omega
          have secondNonempty : second≠[] := by intro empty; simp only [empty,List.length_nil] at secondLong; omega
          obtain ⟨joint,secondHead⟩ : ∃ joint,second.head?=some joint := by
            cases second with
            | nil => exact (secondNonempty rfl).elim
            | cons point tail => exact ⟨point,rfl⟩
          have firstLast := chainParts.1.trans secondHead
          have tailHead := (joinRouteChain_head rest secondNonempty).trans secondHead
          have allContacts : ∀ p,RealContains first p → RealContains (joinRouteChain (second::rest)) p →
              p=realCell joint ∨ ∃ outer,first.head?=some outer ∧
                (joinRouteChain (second::rest)).getLast?=some outer ∧ p=realCell outer := by
            intro p firstContains tailContains
            obtain ⟨route,member,routeContains⟩ := joinRouteChain_contains chainParts.2
              (fun route member => (simple route (List.mem_cons_of_mem first member)).1) tailContains
            obtain ⟨index,valid,atIndex⟩ := List.mem_iff_getElem.mp member
            have indexedContains : RealContains (second::rest)[index] p := by rwa [atIndex]
            have contact := contacts 0 (index+1) (by simp) (Nat.succ_lt_succ valid)
              (by omega) p firstContains indexedContains
            rcases contact with ⟨actual,atLast,equal⟩ | closed
            · exact Or.inl (equal.trans (congrArg realCell (Option.some.inj (atLast.symm.trans firstLast))))
            · obtain ⟨_,final,outer,atHead,atLast,equal⟩ := closed
              have tailLast : (second::rest).getLast?=some route := by
                rw [List.getLast?_eq_getElem?]
                have indexEq : (second::rest).length-1=index := by simp only [List.length_cons] at final ⊢; omega
                rw [indexEq,List.getElem?_eq_getElem valid,atIndex]
              have assembledLast := joinRouteChain_last
                (fun route member => (simple route (List.mem_cons_of_mem first member)).1)
              rw [tailLast,Option.bind_some] at assembledLast
              exact Or.inr ⟨outer,atHead,assembledLast.trans (by simpa only [List.getElem_cons_succ,atIndex] using atLast),equal⟩
          by_cases closed : first.head?=(joinRouteChain (second::rest)).getLast?
          · obtain ⟨outer,firstHead⟩ : ∃ outer,first.head?=some outer := by
              cases first with
              | nil => exact (firstNonempty rfl).elim
              | cons point tail => exact ⟨point,rfl⟩
            apply isRealSimple_join_closed firstSimple tailSimple firstLast tailHead firstHead
              (closed.symm.trans firstHead)
            intro p firstContains tailContains
            rcases allContacts p firstContains tailContains with atJoint | ⟨actual,atHead,_,equal⟩
            · exact Or.inl atJoint
            · exact Or.inr (equal.trans (congrArg realCell (Option.some.inj (atHead.symm.trans firstHead))))
          · apply IsRealOpenSimple.isRealSimple
            apply isRealOpenSimple_join firstSimple tailSimple firstLast tailHead
            intro p firstContains tailContains
            rcases allContacts p firstContains tailContains with atJoint | ⟨outer,atHead,atLast,_⟩
            · exact atJoint
            · exact (closed (atHead.trans atLast.symm)).elim

end LeanTrominoes.GridPolyline
