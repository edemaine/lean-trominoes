/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMThreeStrandRouting
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRoutedTriples
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.OrthogonalPolylineJoin

/-!
# Constructing the three routed 3DM strands

Every source exact-one incidence already has a certified orthogonal route.
This file refines that route, translates three copies onto caller-selected
color lanes, and joins orthogonal endpoint stubs from the checked variable
and clause gadget ports.

The construction proves the exact endpoint and rectilinearity fields of
`ThreeStrandRouting`.  A later global certificate chooses sufficiently
separated layout parameters and proves that the resulting ribbons and local
gadget neighborhoods are pairwise planar.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing

/-- Geometric degrees of freedom for refining one exact-one route into three
colored lanes. -/
structure ThreeStrandLayout where
  factor : Nat
  factorPositive : 0 < factor
  variableOffset : Cell
  clauseOffset : Cell
  laneOffset : WireColor → Cell

/-- Displayed source-clause position at a total numeric index. -/
def positionedClausePositionAt
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (clauseIndex : Nat) : Cell :=
  (source.clauses[clauseIndex]?.map
    (fun clause => clause.position)).getD (0, 0)

/-- The exact source-incidence data belonging to one active variable slot.
This packages the existential correspondence theorem so later route
definitions can use one stable choice. -/
structure OccurrenceSpliceData
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) where
  tagged : TaggedOccurrence Variable
  indexed : CNFIncidence Variable × Nat
  positionedClause : PositionedPeriodicClause Variable
  occurrenceLookup :
    occurrenceAt source.erase entry.1.1 entry.1.2 = some tagged
  indexedMember :
    indexed ∈
      (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx
  metadataEq :
    incidenceTaggedOccurrence indexed.1 = tagged
  clauseMember :
    (positionedClause, indexed.1.clauseIndex) ∈ source.clauses.zipIdx
  routeHead :
    (presentation.variableToClauseRoute indexed.1).head? =
      some (placement.position tagged.1.atom)
  routeLast :
    (presentation.variableToClauseRoute indexed.1).getLast? =
      some (PositionedPeriodicCNF.variableToClauseTarget
        placement positionedClause tagged.1)
  referenceOffset :
    ∀ color,
      (routedOccurrenceReference source.erase
        entry.1.1 entry.1.2 color).offset =
        PeriodicOneInThreeToThreeDM.reverseOffset tagged.1.offset

/-- Every active occurrence has source-incidence splice data. -/
theorem occurrenceSpliceData_nonempty
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    Nonempty (OccurrenceSpliceData presentation entry) := by
  rcases routedOccurrenceSplice presentation entry.1 entry.2 with
    ⟨tagged, indexed, positionedClause, occurrenceLookup,
      indexedMember, metadataEq, clauseMember, routeHead,
      routeLast, referenceOffset⟩
  exact ⟨⟨tagged, indexed, positionedClause, occurrenceLookup,
    indexedMember, metadataEq, clauseMember, routeHead,
    routeLast, referenceOffset⟩⟩

/-- A stable splice-data choice for each active occurrence. -/
noncomputable def occurrenceSpliceData
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    OccurrenceSpliceData presentation entry :=
  Classical.choice (occurrenceSpliceData_nonempty presentation entry)

/-- Scaling a certified orthogonal polyline by a positive integer preserves
orthogonality. -/
theorem orthogonalPolyline_scale
    {points : List Cell} (orthogonal : OrthogonalPolyline points)
    {factor : Nat} (factorPositive : 0 < factor) :
    OrthogonalPolyline (scalePolyline factor points) := by
  unfold OrthogonalPolyline at orthogonal ⊢
  unfold scalePolyline
  apply List.isChain_map_of_isChain
    (Cell.scale factor)
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_scale_iff
        (by exact_mod_cast factorPositive)
        (GridSegment.mk first second)).mpr aligned
  · exact orthogonal

/-- Refined and translated copy of the source incidence route assigned to
one color lane. -/
noncomputable def occurrenceLaneRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  let data := occurrenceSpliceData presentation entry
  translatePolyline (layout.laneOffset color)
    (scalePolyline layout.factor
      (presentation.variableToClauseRoute data.indexed.1))

/-- Exact endpoints of the refined central lane. -/
theorem occurrenceLaneRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    let data := occurrenceSpliceData presentation entry
    (occurrenceLaneRoute presentation layout entry color).head? =
        some (Cell.add (layout.laneOffset color)
          (Cell.scale layout.factor
            (placement.position data.tagged.1.atom))) ∧
      (occurrenceLaneRoute presentation layout entry color).getLast? =
        some (Cell.add (layout.laneOffset color)
          (Cell.scale layout.factor
            (PositionedPeriodicCNF.variableToClauseTarget
              placement data.positionedClause data.tagged.1))) := by
  let data := occurrenceSpliceData presentation entry
  constructor
  · simp [occurrenceLaneRoute, data,
      data.routeHead, translatePolyline]
  · simp [occurrenceLaneRoute, data,
      data.routeLast, translatePolyline]

/-- Every refined central lane remains orthogonal. -/
theorem occurrenceLaneRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (occurrenceLaneRoute presentation layout entry color) := by
  let data := occurrenceSpliceData presentation entry
  have sourceOrthogonal :
      OrthogonalPolyline
        (presentation.variableToClauseRoute data.indexed.1) :=
    presentation.variableToClauseRoute_orthogonal data.indexedMember
  exact
    (orthogonalPolyline_scale sourceOrthogonal
      layout.factorPositive).translate (layout.laneOffset color)

/-- Origin of a checked variable gadget in the refined drawing. -/
def constructedVariableOrigin
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (layout : ThreeStrandLayout) (atom : Variable) : Cell :=
  Cell.add
    (Cell.scale layout.factor (placement.position atom))
    layout.variableOffset

/-- Origin of a checked clause gadget in the refined drawing. -/
def constructedClauseOrigin
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (layout : ThreeStrandLayout) (clauseIndex : Nat) : Cell :=
  Cell.add
    (Cell.scale layout.factor
      (positionedClausePositionAt source clauseIndex))
    layout.clauseOffset

/-- Orthogonal stub from the checked variable-gadget port to the refined
central lane. -/
noncomputable def occurrenceVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  let data := occurrenceSpliceData presentation entry
  PositionedPeriodicCNF.orthogonalDetour
    (Cell.add
      (constructedVariableOrigin placement layout entry.1.1)
      (routedVariablePortPosition source.erase entry color))
    (Cell.add (layout.laneOffset color)
      (Cell.scale layout.factor
        (placement.position data.tagged.1.atom)))

/-- Orthogonal stub from the refined central lane to the checked clause
terminal in its referenced periodic translate. -/
noncomputable def occurrenceClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  let data := occurrenceSpliceData presentation entry
  PositionedPeriodicCNF.orthogonalDetour
    (Cell.add (layout.laneOffset color)
      (Cell.scale layout.factor
        (PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1)))
    (routedClauseTargetPosition source.erase
      (layout.factor * placement.period)
      (constructedClauseOrigin source layout) entry color)

/-- Complete colored corridor obtained by joining the variable stub, refined
source lane, and clause stub. -/
noncomputable def constructedThreeStrandRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  joinAtEndpoint
    (joinAtEndpoint
      (occurrenceVariableStub presentation layout entry color)
      (occurrenceLaneRoute presentation layout entry color))
    (occurrenceClauseStub presentation layout entry color)

/-- The constructed corridor has exactly the endpoints required by the
global typed 3DM assembly. -/
theorem constructedThreeStrandRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (constructedThreeStrandRoute
        presentation layout entry color).head? =
        some (Cell.add
          (constructedVariableOrigin placement layout entry.1.1)
          (routedVariablePortPosition source.erase entry color)) ∧
      (constructedThreeStrandRoute
        presentation layout entry color).getLast? =
        some (routedClauseTargetPosition source.erase
          (layout.factor * placement.period)
          (constructedClauseOrigin source layout) entry color) := by
  let data := occurrenceSpliceData presentation entry
  have laneEndpoints :=
    occurrenceLaneRoute_endpoints presentation layout entry color
  constructor
  · apply joinAtEndpoint_head?
    apply joinAtEndpoint_head?
    exact PositionedPeriodicCNF.orthogonalDetour_head? _ _
  · apply joinAtEndpoint_getLast?
    · apply joinAtEndpoint_getLast?
      · exact PositionedPeriodicCNF.orthogonalDetour_getLast? _ _
      · exact laneEndpoints.1
      · exact laneEndpoints.2
    · exact PositionedPeriodicCNF.orthogonalDetour_head? _ _
    · exact PositionedPeriodicCNF.orthogonalDetour_getLast? _ _

/-- Every constructed colored corridor is rectilinear. -/
theorem constructedThreeStrandRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (constructedThreeStrandRoute
        presentation layout entry color) := by
  have laneEndpoints :=
    occurrenceLaneRoute_endpoints presentation layout entry color
  have variableStubOrthogonal :
      OrthogonalPolyline
        (occurrenceVariableStub presentation layout entry color) := by
    simp only [occurrenceVariableStub]
    exact PositionedPeriodicCNF.orthogonalDetour_orthogonal _ _
  have clauseStubOrthogonal :
      OrthogonalPolyline
        (occurrenceClauseStub presentation layout entry color) := by
    simp only [occurrenceClauseStub]
    exact PositionedPeriodicCNF.orthogonalDetour_orthogonal _ _
  have firstOrthogonal :=
    variableStubOrthogonal.joinAtEndpoint
      (occurrenceLaneRoute_orthogonal
        presentation layout entry color)
      (PositionedPeriodicCNF.orthogonalDetour_getLast? _ _)
      laneEndpoints.1
  apply firstOrthogonal.joinAtEndpoint clauseStubOrthogonal
  · apply joinAtEndpoint_getLast?
    · exact PositionedPeriodicCNF.orthogonalDetour_getLast? _ _
    · exact laneEndpoints.1
    · exact laneEndpoints.2
  · exact PositionedPeriodicCNF.orthogonalDetour_head? _ _

/-- Any certified exact-one incidence presentation supplies the complete
endpoint-and-orthogonality routing interface for the typed 3DM assembly. -/
noncomputable def constructedThreeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (layout : ThreeStrandLayout) :
    ThreeStrandRouting source.erase where
  period := layout.factor * placement.period
  periodPositive :=
    Nat.mul_pos layout.factorPositive presentation.periodPositive
  variableOrigin := constructedVariableOrigin placement layout
  clauseOrigin := constructedClauseOrigin source layout
  route := constructedThreeStrandRoute presentation layout
  routeEndpoints :=
    constructedThreeStrandRoute_endpoints presentation layout
  routeOrthogonal :=
    constructedThreeStrandRoute_orthogonal presentation layout

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
