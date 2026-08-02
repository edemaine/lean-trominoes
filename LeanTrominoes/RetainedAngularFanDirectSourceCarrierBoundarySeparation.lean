import LeanTrominoes.RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation
import LeanTrominoes.RetainedFinalFlatNormalizedBoundary
import LeanTrominoes.OrthogonalPolylineLinearSeparation

/-!
# Routed-clause direct escapes at carrier boundaries

The routed-clause direct atlas has a deliberately wide customized escape,
so it does not fit the ordinary terminal transverse corridor.  It is still
deep inside the routed-clause macrocell, however.  This file expresses each
carrier boundary as an inward-facing linear half-plane and certifies that
every routed-clause escape lies strictly on its inside.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Unit normal pointing from a carrier boundary into its macrocell. -/
def carrierBoundaryInwardNormal : CornerPort → Cell
  | .west => (1, 0)
  | .east => (-1, 0)
  | .south => (0, 1)
  | .north => (0, -1)

/-- The local boundary threshold after the source-clearance scaling and
the complete terminal-fan refinement. -/
def directRefinedCarrierBoundaryValue
    (port : CornerPort) : Int :=
  Cell.linearValue (carrierBoundaryInwardNormal port)
    (Cell.scale
      (retainedTerminalFanTotalRefinement * 4)
      port.position)

/-- The same inward-facing threshold for a macrocell at an arbitrary
unscaled origin. -/
def directRefinedCarrierBoundaryValueAt
    (port : CornerPort) (origin : Cell) : Int :=
  Cell.linearValue (carrierBoundaryInwardNormal port)
    (Cell.scale
      (retainedTerminalFanTotalRefinement * 4)
      (Cell.add origin port.position))

/-- Every point of every customized routed-clause escape is strictly inside
all four refined carrier half-planes of the local macrocell.  The final
application needs only the west, north, or east boundary selected by the
active routed-clause arm; the uniform statement simplifies transport. -/
theorem retainedDirectRoutedClauseFanEscapeAt_strictly_inside_carrierBoundary
    (port : CornerPort) :
    ∀ (index :
        Fin
          (retainedDirectSourcePrefixChoices
            RetainedDirectClauseKind.routedClause).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈
          (retainedDirectSourceFanEscapeAt
            RetainedDirectClauseKind.routedClause
            index slot).route →
        directRefinedCarrierBoundaryValue port <
          Cell.linearValue (carrierBoundaryInwardNormal port) point := by
  cases port <;>
    native_decide

/-- Scaling an outside carrier point by the construction's combined factor
places it on the closed outside of the refined linear threshold. -/
theorem linearValue_scale_le_directRefinedCarrierBoundaryValueAt_of_outside
    (port : CornerPort)
    (origin point : Cell)
    (outside : port.OutsideCarrierBoundaryAt origin point) :
    Cell.linearValue (carrierBoundaryInwardNormal port)
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          point) ≤
      directRefinedCarrierBoundaryValueAt port origin := by
  rcases origin with ⟨originX, originY⟩
  rcases point with ⟨pointX, pointY⟩
  cases port <;>
    simp [CornerPort.OutsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundary,
      carrierBoundaryInwardNormal,
      directRefinedCarrierBoundaryValueAt,
      retainedTerminalFanTotalRefinement_eq,
      CornerPort.position, Cell.linearValue,
      Cell.add, Cell.sub, Cell.scale] at outside ⊢ <;>
    omega

/-- Translating a routed-clause escape to its physical component origin
transports the strict local half-plane certificate to the refined absolute
carrier boundary. -/
theorem
    retainedDirectRoutedClausePositionedFanEscapeAt_strictly_inside_carrierBoundary
    (origin : Cell)
    (port : CornerPort)
    (index :
      Fin
        (retainedDirectSourcePrefixChoices
          RetainedDirectClauseKind.routedClause).length)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset origin)
          (retainedDirectSourceFanEscapeAt
            RetainedDirectClauseKind.routedClause
            index slot).route) :
    directRefinedCarrierBoundaryValueAt port origin <
      Cell.linearValue (carrierBoundaryInwardNormal port) point := by
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    retainedDirectRoutedClauseFanEscapeAt_strictly_inside_carrierBoundary
      port index slot localPoint localPointMember
  rcases origin with ⟨originX, originY⟩
  rcases localPoint with ⟨pointX, pointY⟩
  cases port <;>
    simp [carrierBoundaryInwardNormal,
      directRefinedCarrierBoundaryValue,
      directRefinedCarrierBoundaryValueAt,
      retainedDirectSourceFanPositioningOffset,
      retainedTerminalFanTotalRefinement_eq,
      CornerPort.position, Cell.linearValue,
      Cell.add, Cell.scale] at localBound ⊢ <;>
    omega

/-- A source prefix on the carrier side is strictly separated from every
positioned routed-clause customized escape on the macrocell side. -/
theorem
    retainedScaledOutsidePrefix_strictlyAvoids_positionedRoutedClauseEscape
    (sourceRoute : List Cell)
    (origin : Cell)
    (port : CornerPort)
    (index :
      Fin
        (retainedDirectSourcePrefixChoices
          RetainedDirectClauseKind.routedClause).length)
    (slot : RetainedTerminalSlot)
    (sourceOutside :
      ∀ point ∈ sourceRoute.dropLast,
        port.OutsideCarrierBoundaryAt origin point) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset origin)
        (retainedDirectSourceFanEscapeAt
          RetainedDirectClauseKind.routedClause
          index slot).route) := by
  apply routesStrictlyAvoidEachOther_of_linear_separated
    (carrierBoundaryInwardNormal port)
    (directRefinedCarrierBoundaryValueAt port origin)
  · intro point pointMember
    unfold scalePolyline at pointMember
    rcases List.mem_map.mp pointMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    exact
      linearValue_scale_le_directRefinedCarrierBoundaryValueAt_of_outside
        port origin sourcePoint
        (sourceOutside sourcePoint sourcePointMember)
  · intro point pointMember
    exact
      retainedDirectRoutedClausePositionedFanEscapeAt_strictly_inside_carrierBoundary
        origin port index slot pointMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
