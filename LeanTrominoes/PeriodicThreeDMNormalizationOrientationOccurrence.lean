/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationForwardOrientation

/-!
# Explicit occurrences of normalized orientation sites

The forward orientation is defined by lookup in the finite provenance table.
This module supplies the complementary forward-facing interface: it inserts
known vertex and route sites into that table, evaluates the orientation at an
explicit period translate of any listed site, and relates geometric unit
steps to drawing-lattice neighbors.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- A displayed route window occurs in its recursively generated provenance
list, regardless of how many points precede it. -/
theorem routeOrientationSites_append_mem
    (period : Nat) (edge : ContractedEdge)
    (leading : List Cell) (before current after : Cell) (rest : List Cell) :
    (rasterLocation period current,
        FinalOrientationSite.route edge before current after) ∈
      routeOrientationSites period edge
        (leading ++ before :: current :: after :: rest) := by
  induction leading with
  | nil => simp [routeOrientationSites]
  | cons head tail induction =>
      cases tail with
      | nil => simp [routeOrientationSites]
      | cons next tail =>
          cases tail with
          | nil =>
              simp only [List.nil_append, List.cons_append]
              rw [routeOrientationSites]
              apply List.mem_cons_of_mem
              simpa using induction
          | cons third tail =>
              simp only [List.cons_append]
              rw [routeOrientationSites]
              apply List.mem_cons_of_mem
              simpa using induction

/-- Every listed contracted vertex contributes its finite provenance site. -/
theorem PlanarPresentation.finalOrientationSite_vertex_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices) :
    (rasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition vertex),
      FinalOrientationSite.vertex vertex) ∈
        presentation.finalOrientationSites := by
  unfold PlanarPresentation.finalOrientationSites
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨vertex, vertexMember, rfl⟩

/-- Every displayed window of a listed contracted edge contributes its
finite route provenance site. -/
theorem PlanarPresentation.finalOrientationSite_route_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (leading : List Cell) (before current after : Cell) (rest : List Cell)
    (routeEquation :
      presentation.finalNormalizationRoute edge =
        leading ++ before :: current :: after :: rest) :
    (rasterLocation presentation.finalNormalizationPeriod current,
      FinalOrientationSite.route edge before current after) ∈
        presentation.finalOrientationSites := by
  unfold PlanarPresentation.finalOrientationSites
  apply List.mem_append_right
  simp only [List.mem_flatMap]
  refine ⟨edge, edgeMember, ?_⟩
  rw [routeEquation]
  exact routeOrientationSites_append_mem
    presentation.finalNormalizationPeriod edge leading before current after rest

/-- The forward orientation evaluates to the site's stored semantic value at
every explicit period translate of a listed provenance site. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_periodOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    {storedLocation : Cell} {site : FinalOrientationSite}
    (member :
      (storedLocation, site) ∈
        presentation.toPlanarPresentation.finalOrientationSites)
    (translate : Cell) (side : Side) :
    presentation.forwardDrawingOrientation values
        (reflectedLocation
          (Cell.add
            (site.point presentation.toPlanarPresentation)
            (Cell.scale
              (presentation.toPlanarPresentation.finalNormalizationPeriod : Int)
              translate))) side =
      site.inward presentation.toPlanarPresentation values translate side := by
  let planar := presentation.toPlanarPresentation
  have lookup :=
    planar.finalOrientationSiteAt_reflected_periodOccurrence
      collisionFree member (translate := translate)
  have occurrence :
      reflectedLocation
          (reflectedLocation
            (Cell.add (site.point planar)
              (Cell.scale (planar.finalNormalizationPeriod : Int)
                translate))) =
        Cell.add (site.point planar)
          (Cell.scale (planar.finalNormalizationPeriod : Int) translate) := by
    simp
  have translateEq :=
    planar.finalOrientationSiteOccurrenceTranslate_eq lookup occurrence
  unfold ContinuousPlanarPresentation.forwardDrawingOrientation
  dsimp only
  rw [lookup]
  change site.inward planar values
      (planar.finalOrientationSiteOccurrenceTranslate
        (reflectedLocation
          (Cell.add (site.point planar)
            (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
        site) side =
    site.inward planar values translate side
  rw [translateEq]

/-- A geometric unit step, viewed in reflected drawing coordinates, is the
corresponding drawing-lattice neighbor. -/
theorem latticeNeighbor_reflectedLocation
    (point : Cell) (side : Side) :
    PeriodicOrthogonalDrawing.latticeNeighbor (reflectedLocation point) side =
      reflectedLocation
        (Cell.add point (axisDirectionOfSide side).step) := by
  symm
  simpa using reflectedLocation_add_step point
    (axisDirectionOfSide_isGenuine side)

/-- Adding a unit step before or after a period translation gives the same
geometric occurrence. -/
theorem add_periodTranslation_add_step
    (period : Nat) (point translate : Cell) (side : Side) :
    Cell.add
        (Cell.add point (Cell.scale (period : Int) translate))
        (axisDirectionOfSide side).step =
      Cell.add
        (Cell.add point (axisDirectionOfSide side).step)
        (Cell.scale (period : Int) translate) := by
  rcases point with ⟨pointX, pointY⟩
  rcases translate with ⟨translateX, translateY⟩
  cases side <;>
    simp [Cell.add, Cell.scale, axisDirectionOfSide, AxisDirection.step] <;>
    ring

/-- The drawing neighbor of an explicit period occurrence is the reflected
occurrence of the geometrically adjacent point at the same translate. -/
theorem latticeNeighbor_reflected_periodOccurrence
    (period : Nat) (point translate : Cell) (side : Side) :
    PeriodicOrthogonalDrawing.latticeNeighbor
        (reflectedLocation
          (Cell.add point (Cell.scale (period : Int) translate))) side =
      reflectedLocation
        (Cell.add
          (Cell.add point (axisDirectionOfSide side).step)
          (Cell.scale (period : Int) translate)) := by
  rw [latticeNeighbor_reflectedLocation]
  rw [add_periodTranslation_add_step]

end PeriodicThreeDM

end LeanTrominoes
