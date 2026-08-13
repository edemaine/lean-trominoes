/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellBounds
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes

/-!
# Pointwise bounds for assembled ribbon corridors

Each listed point of a colored corridor core belongs to the closed refined
block of some lattice point on its unit source route.  This is the
route-level bridge from the finite macrocell bounds to global periodic
coordinate bounds and to separation from endpoint fans in distant blocks.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- A standard ribbon exit lies in its translated owning block. -/
theorem ribbonMacrocellExit_bounded
    (center : Cell) (direction : AxisDirection)
    (color : WireColor) :
    InRibbonMacrocell center
      (ribbonMacrocellExit center direction color) := by
  apply inRibbonMacrocell_add_origin
  cases direction <;> cases color <;>
    native_decide

/-- Every point of a corridor core belongs to the owning block of some
listed source-route point. -/
theorem ribbonCorridorCore_points_bounded
    (color : WireColor) (first second : Cell)
    (rest : List Cell) {point : Cell}
    (member :
      point ∈ ribbonCorridorCore color
        (first :: second :: rest)) :
    ∃ center ∈ first :: second :: rest,
      InRibbonMacrocell center point := by
  induction rest generalizing first second with
  | nil =>
      simp only [ribbonCorridorCore_pair,
        List.mem_singleton] at member
      subst point
      exact
        ⟨first, by simp,
          ribbonMacrocellExit_bounded first
            (AxisDirection.between first second) color⟩
  | cons third rest induction =>
      cases rest with
      | nil =>
          rw [ribbonCorridorCore] at member
          exact
            ⟨second, by simp,
              ribbonMacrocellRoute_points_bounded
                second
                (AxisDirection.between first second)
                (AxisDirection.between second third)
                color point member⟩
      | cons fourth rest =>
          rw [ribbonCorridorCore] at member
          rcases mem_joinAtEndpoint member with
              leadingMember | trailingMember
          · exact
              ⟨second, by simp,
                ribbonMacrocellRoute_points_bounded
                  second
                  (AxisDirection.between first second)
                  (AxisDirection.between second third)
                  color point leadingMember⟩
          · rcases
                induction
                  (first := second) (second := third)
                  trailingMember with
              ⟨center, centerMember, bounded⟩
            exact
              ⟨center, by
                simp only [List.mem_cons] at centerMember ⊢
                exact Or.inr centerMember,
                bounded⟩

/-- Every point of an active occurrence's colored corridor core lies in a
block owned by some point of its selected unit source route. -/
theorem occurrenceRibbonCorridorCore_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) {point : Cell}
    (member :
      point ∈ occurrenceRibbonCorridorCore
        presentation entry color) :
    ∃ center ∈ occurrenceUnitSourceRoute presentation entry,
      InRibbonMacrocell center point := by
  have length :=
    occurrenceUnitSourceRoute_length presentation entry
  cases routeEquation :
      occurrenceUnitSourceRoute presentation entry with
  | nil =>
      simp [routeEquation] at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp [routeEquation] at length
      | cons second rest =>
          have bounded :=
            ribbonCorridorCore_points_bounded
              (routedRibbonLane source.erase entry color)
              first second rest
              (by
                simpa [occurrenceRibbonCorridorCore,
                  routeEquation] using member)
          simpa [routeEquation] using bounded

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
