/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OctilinearPolylineRasterization
import LeanTrominoes.PlanarThreeSATTerminalPortCertificates
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Octilinear embedded-CNF incidence drawings

This file packages the pointwise property needed before rasterizing the
retained planar-SAT routes: every genuine incidence route consists only of
nondegenerate axis or 45-degree segments.

The certificate is stable under the two operations used to place fixed
gadgets, namely coordinate translation and logical-variable renaming.
Orthogonal drawings satisfy it automatically, while a direct incidence
drawing satisfies it whenever its clause-to-variable terminal rays have the
existing eight-direction certificate.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- Every nondegenerate axis-aligned segment is a valid octilinear segment. -/
theorem terminalPort_sub_isSome_of_isAxisAligned
    (segment : GridSegment)
    (aligned : segment.IsAxisAligned) :
    (terminalPort
      (Cell.sub segment.finish segment.start)).isSome := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rw [terminalPort_isSome_iff]
  simp only [Cell.sub, Prod.mk.injEq, ne_eq]
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical] at aligned
  omega

/-- Reversing a vector does not change whether it lies on one of the eight
nonzero compass rays. -/
theorem terminalPort_sub_swap_isSome_iff
    (first second : Cell) :
    (terminalPort (Cell.sub first second)).isSome ↔
      (terminalPort (Cell.sub second first)).isSome := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rw [terminalPort_isSome_iff, terminalPort_isSome_iff]
  simp only [Cell.sub, Prod.mk.injEq, ne_eq]
  omega

/-- Every orthogonal polyline is in particular octilinear. -/
theorem OctilinearPolyline.of_orthogonal
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    OctilinearPolyline points := by
  rw [PeriodicOrthocrossing.orthogonalPolyline_iff_segments]
    at orthogonal
  intro segment segmentMember
  exact terminalPort_sub_isSome_of_isAxisAligned
    segment (orthogonal segment segmentMember)

/-- Common translation preserves every segment's compass class. -/
theorem OctilinearPolyline.translate
    {points : List Cell}
    (octilinear : OctilinearPolyline points)
    (offset : Cell) :
    OctilinearPolyline
      (points.map (Cell.add offset)) := by
  intro translatedSegment translatedSegmentMember
  rw [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
    at translatedSegmentMember
  rcases List.mem_map.mp translatedSegmentMember with
    ⟨segment, segmentMember, rfl⟩
  simpa [GridSegment.translate, Cell.add, Cell.sub] using
    octilinear segment segmentMember

end PeriodicEightOccurrenceSplit

namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

open PeriodicEightOccurrenceSplit

/-- Every genuine route of a finite embedded-CNF drawing is octilinear. -/
def RoutesOctilinear
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    OctilinearPolyline
      (drawing.routeAt (drawing.incidenceAt incidenceIndex))

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.RoutesOctilinear := by
  unfold RoutesOctilinear OctilinearPolyline incidenceAt incidences routeAt
  infer_instance

/-- An orthogonal finite drawing is automatically octilinear. -/
theorem RoutesOctilinear.of_isOrthogonal
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (orthogonal : drawing.IsOrthogonal) :
    drawing.RoutesOctilinear := by
  intro incidenceIndex
  apply OctilinearPolyline.of_orthogonal
  rw [PeriodicOrthocrossing.orthogonalPolyline_iff_segments]
  intro segment segmentMember
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, rfl⟩
  exact orthogonal incidenceIndex segmentIndex

/-- Translation preserves route octilinearity. -/
theorem RoutesOctilinear.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (octilinear : drawing.RoutesOctilinear)
    (offset : Cell) :
    (drawing.translate offset).RoutesOctilinear := by
  intro translatedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  rw [incidenceEqual, routeAt_translate_incidence]
  exact (octilinear originalIndex).translate offset

/-- Logical-variable renaming changes no route coordinates. -/
theorem RoutesOctilinear.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (octilinear : drawing.RoutesOctilinear)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename variableMap targetPosition).RoutesOctilinear := by
  intro renamedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
  exact octilinear originalIndex

/-- Because renaming changes neither route coordinates nor presentation
indices, an octilinearity certificate can also be pulled back through a
rename. -/
theorem RoutesOctilinear.of_rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
  (octilinear :
      (drawing.rename
        variableMap targetPosition).RoutesOctilinear) :
    drawing.RoutesOctilinear := by
  intro originalIndex
  let renamedIndex :
      Fin (drawing.rename
        variableMap targetPosition).incidences.length :=
    ⟨originalIndex.val, by
      simpa only [rename_incidences_length] using
        originalIndex.isLt⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  have renamedRoute := octilinear renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
    at renamedRoute
  exact renamedRoute

/-- Membership-style form of the finite octilinearity certificate. -/
theorem routesOctilinear_iff
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    drawing.RoutesOctilinear ↔
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ drawing.formula.zipIdx →
          ∀ literal literalIndex,
            (literal, literalIndex) ∈ clause.literals.zipIdx →
              OctilinearPolyline
                (drawing.routes clauseIndex literalIndex) := by
  constructor
  · intro octilinear clause clauseIndex clauseMember
      literal literalIndex literalMember
    let incidence : EmbeddedCNFIncidence Variable :=
      ⟨clause, clauseIndex, literal, literalIndex⟩
    have incidenceMember :
        incidence ∈ drawing.incidences := by
      exact
        (mem_embeddedCNFIncidences_iff
          drawing.formula incidence).mpr
          ⟨clauseMember, literalMember⟩
    rcases List.mem_iff_get.mp incidenceMember with
      ⟨incidenceIndex, incidenceEqual⟩
    have routeOctilinear := octilinear incidenceIndex
    have incidenceAtEqual :
        drawing.incidenceAt incidenceIndex = incidence := by
      exact incidenceEqual
    rw [incidenceAtEqual] at routeOctilinear
    exact routeOctilinear
  · intro octilinear incidenceIndex
    let incidence := drawing.incidenceAt incidenceIndex
    have incidenceMember :
        incidence ∈ drawing.incidences :=
      List.get_mem drawing.incidences incidenceIndex
    have indexedMembers :=
      (mem_embeddedCNFIncidences_iff
        drawing.formula incidence).mp incidenceMember
    exact octilinear
      incidence.clause incidence.clauseIndex indexedMembers.1
      incidence.literal incidence.literalIndex indexedMembers.2

/-- A direct clause-to-variable route is octilinear when its backwards
terminal vector has a valid compass class. -/
theorem straightIncidenceRoute_octilinear
    {source target : Cell}
    (valid :
      (terminalPort (Cell.sub source target)).isSome) :
    OctilinearPolyline
      (straightIncidenceRoute source target) := by
  intro segment segmentMember
  simp only [straightIncidenceRoute, gridPolylineSegments,
    List.mem_cons] at segmentMember
  rcases segmentMember with rfl | impossible
  · exact
      (terminalPort_sub_swap_isSome_iff source target).mp valid
  · contradiction

/-- The finite compass-terminal certificate makes every route of the
corresponding direct incidence drawing octilinear. -/
theorem straightIncidenceDrawing_routesOctilinear
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell)
    (valid :
      EmbeddedTerminalPortsValid formula variablePosition) :
    (straightIncidenceDrawing
      formula variablePosition).RoutesOctilinear := by
  intro incidenceIndex
  let incidence :=
    (straightIncidenceDrawing
      formula variablePosition).incidenceAt incidenceIndex
  have incidenceMember :
      incidence ∈
        (straightIncidenceDrawing
          formula variablePosition).incidences :=
    List.get_mem _ incidenceIndex
  have indexedMembers :=
    (mem_embeddedCNFIncidences_iff formula incidence).mp
      incidenceMember
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp indexedMembers.1
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp indexedMembers.2
  have terminalValid :=
    (embeddedTerminalPortsValid_iff
      formula variablePosition).mp valid
      incidence.clause
      (List.fst_mem_of_mem_zipIdx indexedMembers.1)
      incidence.literal
      (List.fst_mem_of_mem_zipIdx indexedMembers.2)
  change
    OctilinearPolyline
      (straightIncidenceRoutes formula variablePosition
        incidence.clauseIndex incidence.literalIndex)
  simp only [straightIncidenceRoutes, clauseLookup, literalLookup]
  exact straightIncidenceRoute_octilinear terminalValid

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
