/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity
import LeanTrominoes.PeriodicGridDrawingEndpointContacts

/-!
# Indexed route-point consequences of finite incidence planarity

Finite incidence planarity advertises a shared point as the geometric head
or last point of both routes.  Periodic ribbon infrastructure instead uses
the point's syntactic list index.  Route simplicity makes those two views
equivalent, because a simple route has no duplicate listed points.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- On a duplicate-free route, a same-indexed listed point advertised as a
geometric route endpoint has first or last syntactic index. -/
theorem indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
    {route : List Cell}
    (nodup : route.Nodup)
    {taggedPoint : Cell × Nat}
    (pointMember : taggedPoint ∈ route.zipIdx)
    (endpoint :
      RoutePointIsEndpoint route taggedPoint.1) :
    ({ routeIndex := 0
       pointIndex := taggedPoint.2
       routeLength := route.length
       point := taggedPoint.1 } : IndexedRoutePoint).IsEndpoint := by
  have pointIndexLt : taggedPoint.2 < route.length :=
    List.snd_lt_of_mem_zipIdx pointMember
  let pointIndex : Fin route.length :=
    ⟨taggedPoint.2, pointIndexLt⟩
  have pointAt :
      route.get pointIndex = taggedPoint.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp pointMember)).2
  have routeNonempty : route ≠ [] := by
    intro empty
    subst route
    simp at pointIndexLt
  rcases endpoint with headEndpoint | lastEndpoint
  · left
    have headEq :
        route.head routeNonempty = taggedPoint.1 := by
      rw [List.head?_eq_some_head routeNonempty] at headEndpoint
      exact Option.some.inj headEndpoint
    have zeroIndexLt : 0 < route.length :=
      List.length_pos_iff.mpr routeNonempty
    let zeroIndex : Fin route.length :=
      ⟨0, zeroIndexLt⟩
    have zeroAt :
        route.get zeroIndex = taggedPoint.1 := by
      change route[0] = taggedPoint.1
      rw [← List.head_eq_getElem_zero routeNonempty]
      exact headEq
    have indexEq : pointIndex = zeroIndex :=
      nodup.injective_get (pointAt.trans zeroAt.symm)
    exact congrArg Fin.val indexEq
  · right
    have lastEq :
        route.getLast routeNonempty = taggedPoint.1 := by
      rw [List.getLast?_eq_getLast_of_ne_nil routeNonempty]
        at lastEndpoint
      exact Option.some.inj lastEndpoint
    have lastIndexLt :
        route.length - 1 < route.length := by
      omega
    let lastIndex : Fin route.length :=
      ⟨route.length - 1, lastIndexLt⟩
    have lastAt :
        route.get lastIndex = taggedPoint.1 := by
      exact
        (List.get_length_sub_one lastIndexLt).trans lastEq
    have indexEq : pointIndex = lastIndex :=
      nodup.injective_get (pointAt.trans lastAt.symm)
    have valueEq := congrArg Fin.val indexEq
    simp only [pointIndex, lastIndex] at valueEq
    change taggedPoint.2 + 1 = route.length
    omega

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
