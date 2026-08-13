/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreMacrocellSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseCoordinatedFans
import LeanTrominoes.OrthogonalPolylineBoundingBox

/-!
# Variable-site cores versus neighboring clause fans

The routed finite variable-site core lies in the one-cell inset rectangle
`[1,127] × [1,127]`.  Every coordinated clause fan lies in its closed
standard macrocell.  Consequently translating such a fan to any of the eight
neighboring macrocells leaves a strict coordinate gap between the routes.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every routed finite variable-site core lies in the strict one-cell inset
of the standard ribbon macrocell. -/
theorem routedVariableSiteRoute_points_in_inset_rectangle :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot)
      (active : slot.index < countPred + 1)
      (color : WireColor)
      (point : Cell),
      point ∈
          translatePolyline standardThreeStrandLayout.variableOffset
            ((variableSiteDrawing (countPred + 1) kind polarity).route
              ⟨(VariableRibbonFanData.routedTriple
                  ⟨countPred, kind, polarity, fun _ => .invalid⟩
                  slot color),
                VariableRibbonFanData.routedTriple_matches
                  ⟨countPred, kind, polarity, fun _ => .invalid⟩
                  slot active color⟩
              color) →
        InClosedGridRectangle (1, 1) (127, 127) point := by
  native_decide

namespace VariableRibbonFanData

/-- Data-packaged inset bound for a routed finite variable-site core. -/
theorem routedVariableSiteRoute_points_in_inset_rectangle
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    {point : Cell}
    (member :
      point ∈
        translatePolyline standardThreeStrandLayout.variableOffset
          ((variableSiteDrawing data.count data.kind data.polarity).route
            (data.activeRoutedTriple slot active color) color)) :
    InClosedGridRectangle (1, 1) (127, 127) point := by
  exact LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.routedVariableSiteRoute_points_in_inset_rectangle
    data.countPred data.kind data.polarity slot active color point member

/-- A routed variable-site core strictly avoids any route bounded in a
neighboring closed standard ribbon macrocell. -/
theorem routedVariableSiteRoute_strictlyAvoids_translated_bounded_route_of_adjacent
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (offset : Cell)
    (adjacent : RibbonMacrocellOffsetAdjacent offset)
    (second : List Cell)
    (secondBounded :
      ∀ point ∈ second, InStandardRibbonMacrocell point) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active color) color))
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        second) := by
  apply routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower := (1, 1)) (firstUpper := (127, 127))
      (secondLower :=
        Cell.scale standardThreeStrandLayout.factor offset)
      (secondUpper :=
        Cell.add
          (Cell.scale standardThreeStrandLayout.factor offset)
          (128, 128))
  · intro point member
    exact data.routedVariableSiteRoute_points_in_inset_rectangle
      slot active color member
  · intro point member
    unfold translatePolyline at member
    rcases List.mem_map.mp member with
      ⟨localPoint, localMember, rfl⟩
    have bounded := secondBounded localPoint localMember
    rcases offset with ⟨offsetX, offsetY⟩
    rcases localPoint with ⟨localX, localY⟩
    simp only [InStandardRibbonMacrocell,
      InClosedGridRectangle, standardThreeStrandLayout,
      Cell.add, Cell.scale] at bounded ⊢
    omega
  · rcases offset with ⟨offsetX, offsetY⟩
    simp only [RibbonMacrocellOffsetAdjacent,
      ClosedGridRectanglesSeparated,
      standardThreeStrandLayout, Cell.scale, Cell.add]
      at adjacent ⊢
    by_cases offsetXZero : offsetX = 0
    · have offsetYNe : offsetY ≠ 0 := by
        intro offsetYZero
        apply adjacent.2.2.2.2
        exact Prod.ext offsetXZero offsetYZero
      omega
    · omega

/-- In particular, the routed variable-site core strictly avoids every
complete coordinated clause fan translated to a neighboring macrocell. -/
theorem routedVariableSiteRoute_strictlyAvoids_adjacentClauseCoordinatedRoute
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (clauseData : ClauseRibbonFanData)
    (clauseCompatible : clauseData.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (groupActive : clauseData.GroupActive group)
    (lane : WireColor)
    (offset : Cell)
    (adjacent : RibbonMacrocellOffsetAdjacent offset) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active color) color))
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (clauseData.coordinatedRoute group lane)) := by
  exact
    data.routedVariableSiteRoute_strictlyAvoids_translated_bounded_route_of_adjacent
      slot active color offset adjacent
      (clauseData.coordinatedRoute group lane)
      (fun point member =>
        clauseData.coordinatedRoute_points_bounded
          clauseCompatible group groupActive lane member)

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
