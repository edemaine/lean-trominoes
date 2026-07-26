import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorSeparation
import LeanTrominoes.PeriodicGridDrawingNoImmediateReversal
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionSimplicity

/-!
# Unit source routes for 3DM ribbon corridors

This file specializes ordered unit subdivision to every active exact-one
incidence selected by the 3DM reduction.  The resulting source route retains
its exact variable and clause endpoints, has at least two points, remains
orthogonal, and consists entirely of genuine cardinal unit steps.

Continuous planarity excludes immediate reversals on the stored incidence
route.  This property survives reversal, rebasing, and unit subdivision, so
the assembled colored macrocell core is unconditionally rectilinear for a
continuously planar presentation.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The source incidence route with every axis-aligned segment subdivided
into ordered unit lattice steps. -/
noncomputable def occurrenceUnitSourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) : List Cell :=
  AxisDirection.unitSubdividePolyline
    (occurrenceSourceRoute presentation entry)

/-- The selected rebased source route remains orthogonal. -/
theorem occurrenceSourceRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    OrthogonalPolyline
      (occurrenceSourceRoute presentation entry) := by
  exact
    presentation.variableToClauseRoute_orthogonal
      (occurrenceSpliceData presentation entry).indexedMember

/-- Reversing and rebasing a continuously planar incidence route preserves
its no-immediate-reversal certificate. -/
theorem variableToClauseRoute_hasNoImmediateReversal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    AxisDirection.HasNoImmediateReversal
      (presentation.toPlanarIncidencePresentation
        |>.variableToClauseRoute tagged.1) := by
  have originalNoReversal :=
    presentation.route_hasNoImmediateReversal_of_tagged
      taggedMember
  have originalOrthogonal :=
    presentation.toPlanarIncidencePresentation
      |>.route_orthogonal_of_tagged taggedMember
  have reversedNoReversal :=
    originalNoReversal.reverse originalOrthogonal
  unfold
    PositionedPeriodicCNF.PlanarIncidencePresentation.variableToClauseRoute
    PeriodicOrthocrossing.translatePolyline
  exact reversedNoReversal.translate _

/-- Every rebased active occurrence route from a continuously planar source
has no immediate reversal. -/
theorem occurrenceSourceRoute_hasNoImmediateReversal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    AxisDirection.HasNoImmediateReversal
      (occurrenceSourceRoute
        presentation.toPlanarIncidencePresentation entry) := by
  let planar :=
    presentation.toPlanarIncidencePresentation
  let data := occurrenceSpliceData planar entry
  exact
    variableToClauseRoute_hasNoImmediateReversal
      presentation data.indexedMember

/-- Reversing and rebasing a tagged route from a ribbon-ready presentation
preserves its finite simplicity certificate. -/
theorem variableToClauseRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (presentation.toPlanarIncidencePresentation
        |>.variableToClauseRoute tagged.1) := by
  have originalSimple :=
    presentation.routeIsSimple_of_tagged taggedMember
  have reversedSimple := originalSimple.reverse
  unfold
    PositionedPeriodicCNF.PlanarIncidencePresentation.variableToClauseRoute
    PeriodicOrthocrossing.translatePolyline
  exact routeIsSimple_translate reversedSimple _

/-- Every active occurrence source route selected from a ribbon-ready
presentation is simple after reversal and periodic rebasing. -/
theorem occurrenceSourceRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    LocalIncidenceDrawing.RouteIsSimple
      (occurrenceSourceRoute
        presentation.toPlanarIncidencePresentation entry) := by
  let planar := presentation.toPlanarIncidencePresentation
  let data := occurrenceSpliceData planar entry
  exact
    variableToClauseRoute_isSimple
      presentation data.indexedMember

/-- The unitized source route remains orthogonal. -/
theorem occurrenceUnitSourceRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    OrthogonalPolyline
      (occurrenceUnitSourceRoute presentation entry) := by
  exact
    AxisDirection.unitSubdividePolyline_orthogonal
      (occurrenceSourceRoute_orthogonal presentation entry)

/-- Every consecutive pair on the unitized occurrence route is exactly one
genuine cardinal step. -/
theorem occurrenceUnitSourceRoute_unitSteps
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (occurrenceUnitSourceRoute presentation entry).IsChain
      AxisDirection.IsUnitAxisStep := by
  exact
    AxisDirection.unitSubdividePolyline_unitSteps
      (occurrenceSourceRoute_orthogonal presentation entry)

/-- Unit subdivision preserves the no-reversal certificate inherited from
continuous planarity. -/
theorem occurrenceUnitSourceRoute_hasNoImmediateReversal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    SourceRouteHasNoImmediateReversal
      (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry) := by
  exact
    AxisDirection.unitSubdividePolyline_hasNoImmediateReversal
      (occurrenceSourceRoute_orthogonal
        presentation.toPlanarIncidencePresentation entry)
      (occurrenceSourceRoute_hasNoImmediateReversal
        presentation entry)

/-- Unit subdivision of an active simple occurrence route introduces no
duplicate lattice points. -/
theorem occurrenceUnitSourceRoute_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (occurrenceUnitSourceRoute
      presentation.toPlanarIncidencePresentation entry).Nodup := by
  exact
    AxisDirection.unitSubdividePolyline_nodup
      (occurrenceSourceRoute_orthogonal
        presentation.toPlanarIncidencePresentation entry)
      (occurrenceSourceRoute_isSimple presentation entry)

/-- Unit subdivision cannot collapse a genuine incidence route below two
points. -/
theorem occurrenceUnitSourceRoute_length
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    2 ≤ (occurrenceUnitSourceRoute presentation entry).length := by
  have sourceLength :=
    occurrenceSourceRoute_length presentation entry
  have sourceOrthogonal :=
    occurrenceSourceRoute_orthogonal presentation entry
  cases sourceEquation :
      occurrenceSourceRoute presentation entry with
  | nil =>
      simp [sourceEquation] at sourceLength
  | cons first rest =>
      cases rest with
      | nil =>
          simp [sourceEquation] at sourceLength
      | cons second rest =>
          simpa [occurrenceUnitSourceRoute, sourceEquation] using
            AxisDirection.unitSubdividePolyline_length_ge_two
              (first := first) (second := second)
              (rest := rest)
              (by simpa [sourceEquation] using sourceOrthogonal)

/-- Unit subdivision retains the selected incidence's exact source and
target endpoints. -/
theorem occurrenceUnitSourceRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    (occurrenceUnitSourceRoute presentation entry).head? =
        some (placement.position data.tagged.1.atom) ∧
      (occurrenceUnitSourceRoute presentation entry).getLast? =
        some (PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1) := by
  let data := occurrenceSpliceData presentation entry
  have nonempty :
      occurrenceSourceRoute presentation entry ≠ [] := by
    intro empty
    have length :=
      occurrenceSourceRoute_length presentation entry
    rw [empty] at length
    simp at length
  constructor
  · rw [occurrenceUnitSourceRoute,
      AxisDirection.unitSubdividePolyline_head? nonempty]
    exact data.routeHead
  · rw [occurrenceUnitSourceRoute,
      AxisDirection.unitSubdividePolyline_getLast?
        nonempty
        (occurrenceSourceRoute_orthogonal
          presentation entry)]
    exact data.routeLast

/-- The endpoint-certified macrocell core assigned to one occurrence and
color. -/
noncomputable def occurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  ribbonCorridorCore color
    (occurrenceUnitSourceRoute presentation entry)

/-- Exact half-edge-boundary endpoints of the occurrence's colored core. -/
theorem occurrenceRibbonCorridorCore_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (occurrenceRibbonCorridorCore
        presentation entry color).head? =
        some (ribbonCorridorRouteStart color
          (occurrenceUnitSourceRoute presentation entry)) ∧
      (occurrenceRibbonCorridorCore
        presentation entry color).getLast? =
        some (ribbonCorridorRouteEnd color
          (occurrenceUnitSourceRoute presentation entry)) := by
  exact
    ribbonCorridorCore_endpoints_of_length_ge_two color
      (occurrenceUnitSourceRoute_length presentation entry)
      (occurrenceUnitSourceRoute_unitSteps presentation entry)

/-- An explicit no-reversal certificate suffices to make an occurrence's
macrocell core rectilinear. -/
theorem occurrenceRibbonCorridorCore_orthogonal_of_noImmediateReversal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (occurrenceUnitSourceRoute presentation entry)) :
    OrthogonalPolyline
      (occurrenceRibbonCorridorCore
        presentation entry color) := by
  exact
    ribbonCorridorCore_orthogonal_of_length_ge_two color
      (occurrenceUnitSourceRoute_length presentation entry)
      (occurrenceUnitSourceRoute_unitSteps presentation entry)
      noReversal

/-- Every occurrence corridor core inherited from a continuously planar
source drawing is rectilinear. -/
theorem occurrenceRibbonCorridorCore_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation
        entry color) := by
  exact
    occurrenceRibbonCorridorCore_orthogonal_of_noImmediateReversal
      presentation.toPlanarIncidencePresentation
      entry color
      (occurrenceUnitSourceRoute_hasNoImmediateReversal
        presentation entry)

/-- The differently colored ribbon cores placed along one active occurrence
route are separated without any point or interior contact. -/
theorem occurrenceRibbonCorridorCores_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    {firstColor secondColor : WireColor}
    (colorsDifferent : firstColor ≠ secondColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation
        entry firstColor)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation
        entry secondColor) := by
  let points :=
    occurrenceUnitSourceRoute
      presentation.toPlanarIncidencePresentation entry
  have length :=
    occurrenceUnitSourceRoute_length
      presentation.toPlanarIncidencePresentation entry
  cases pointsEquation : points with
  | nil =>
      simp [pointsEquation, points] at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp [pointsEquation, points] at length
      | cons second rest =>
          simpa [occurrenceRibbonCorridorCore,
            points, pointsEquation] using
            ribbonCorridorCores_strictlyAvoidEachOther
              colorsDifferent first second rest
              (by
                simpa [points, pointsEquation] using
                  occurrenceUnitSourceRoute_unitSteps
                    presentation.toPlanarIncidencePresentation
                    entry)
              (by
                simpa [points, pointsEquation] using
                  occurrenceUnitSourceRoute_hasNoImmediateReversal
                    presentation.toContinuousPlanarIncidencePresentation
                    entry)
              (by
                simpa [points, pointsEquation] using
                  occurrenceUnitSourceRoute_nodup
                    presentation entry)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
