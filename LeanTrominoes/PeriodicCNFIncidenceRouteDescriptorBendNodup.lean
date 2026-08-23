/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorBendEnumeration
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEdgeIndexNodup
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorNodup
import LeanTrominoes.PeriodicCNFPlanarOccurrences

/-! # Duplicate-freedom of numeric incidence-route bends -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Consecutive bend enumeration never repeats an incoming segment index. -/
theorem routeBendsAux_incomingSegmentIndices_nodup
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat),
      ((routeBendsAux routeIndex translate startIndex points).map
        RouteBend.incomingSegmentIndex).Nodup := by
  intro points
  induction points with
  | nil => intro startIndex; simp [routeBendsAux]
  | cons first rest induction =>
      cases rest with
      | nil => intro startIndex; simp [routeBendsAux]
      | cons second rest =>
          cases rest with
          | nil => intro startIndex; simp [routeBendsAux]
          | cons third rest =>
              intro startIndex
              simp only [routeBendsAux, List.map_cons, List.nodup_cons]
              constructor
              · intro headIndexMember
                rcases List.mem_map.mp headIndexMember with
                  ⟨routeBend, routeBendMember, indexEq⟩
                have memberData :=
                  routeBendsAux_member_data routeIndex translate
                    (second :: third :: rest) (startIndex + 1)
                    routeBendMember
                omega
              · exact induction (startIndex + 1)

/-- One route occurrence's bend list is duplicate-free. -/
theorem routeBends_nodup
    (routeIndex : Nat) (translate : Cell) (route : List Cell) :
    (routeBends routeIndex translate route).Nodup := by
  apply (routeBendsAux_incomingSegmentIndices_nodup
    routeIndex translate route 0).of_map

/-- The nine neighboring bend occurrences of one route are duplicate-free. -/
theorem neighborRouteBends_nodup
    (routeIndex : Nat) (route : List Cell) :
    (neighborTranslations.flatMap fun translate =>
      routeBends routeIndex translate route).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro translate _translateMember
    exact routeBends_nodup routeIndex translate route
  · exact
      (List.nodup_iff_pairwise_ne.mp neighborTranslations_nodup).imp fun
        {firstTranslate secondTranslate} translatesNe => by
          unfold Function.onFun
          rw [List.disjoint_left]
          intro routeBend firstMember secondMember
          unfold routeBends at firstMember secondMember
          have firstData :=
            routeBendsAux_member_data routeIndex firstTranslate
              route 0 firstMember
          have secondData :=
            routeBendsAux_member_data routeIndex secondTranslate
              route 0 secondMember
          exact translatesNe
            (firstData.2.1.symm.trans secondData.2.1)

end PeriodicOrthocrossing

namespace PeriodicCNF

open PeriodicOrthocrossing

/-- The complete numeric route-major neighboring bend enumeration is
duplicate-free. -/
theorem numericRouteDescriptorBends_nodup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((numericRouteDescriptors formula).flatMap fun descriptor =>
      neighborTranslations.flatMap fun translate =>
        routeBends descriptor.edgeIndex translate descriptor.route).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro descriptor _descriptorMember
    exact neighborRouteBends_nodup
      descriptor.edgeIndex descriptor.route
  · have pairwiseIndices :
        (numericRouteDescriptors formula).Pairwise
          (fun first second =>
            first.edgeIndex ≠ second.edgeIndex) := by
      rw [← List.pairwise_map]
      exact List.nodup_iff_pairwise_ne.mp
        (numericRouteDescriptor_edgeIndices_nodup formula)
    exact pairwiseIndices.imp fun
      {firstDescriptor secondDescriptor} edgeIndicesNe => by
        unfold Function.onFun
        rw [List.disjoint_left]
        intro routeBend firstMember secondMember
        rcases List.mem_flatMap.mp firstMember with
          ⟨firstTranslate, _firstTranslateMember, firstBendMember⟩
        rcases List.mem_flatMap.mp secondMember with
          ⟨secondTranslate, _secondTranslateMember, secondBendMember⟩
        unfold routeBends at firstBendMember secondBendMember
        have firstData :=
          routeBendsAux_member_data firstDescriptor.edgeIndex
            firstTranslate firstDescriptor.route 0 firstBendMember
        have secondData :=
          routeBendsAux_member_data secondDescriptor.edgeIndex
            secondTranslate secondDescriptor.route 0 secondBendMember
        exact edgeIndicesNe (firstData.1.symm.trans secondData.1)

/-- Consequently the semantic drawing's bend enumeration needs no
deduplication. -/
theorem incidenceGraph_drawingRouteBends_nodup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingRouteBends formula.incidenceGraph).Nodup := by
  rw [incidenceGraph_drawingRouteBends_eq_numeric]
  exact numericRouteDescriptorBends_nodup formula

@[simp]
theorem incidenceGraph_drawingRouteBends_dedup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingRouteBends formula.incidenceGraph).dedup =
      drawingRouteBends formula.incidenceGraph := by
  exact List.dedup_eq_self.mpr
    (incidenceGraph_drawingRouteBends_nodup formula)

end PeriodicCNF
end LeanTrominoes
