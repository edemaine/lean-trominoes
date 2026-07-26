import LeanTrominoes.OrthogonalPolylineElbow
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirections
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRouteBounds

/-!
# Block-local ribbon endpoint fans

The central ribbon corridor stops at the boundary of the source variable and
clause macrocells.  This file connects those boundary points to the exact
finite-gadget ports using one-bend routes that remain in the coordinate box
of their endpoints.

The variable fan approaches its boundary point parallel to the outgoing
source edge.  Dually, the clause fan leaves its boundary point parallel to
the incoming source edge.  Pairwise nonintersection of all fans at one
source vertex is a later finite geometric certificate.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing

/-- Local variable-side fan from a finite gadget port to one colored ribbon
exit.  The final segment is parallel to the advertised source direction. -/
def standardVariableRibbonFan
    (port : Cell) (direction : AxisDirection)
    (color : WireColor) : List Cell :=
  match direction with
  | .east | .west =>
      verticalFirstElbow port
        (standardRibbonMacrocellExit direction color)
  | .north | .south | .invalid =>
      horizontalFirstElbow port
        (standardRibbonMacrocellExit direction color)

/-- Local clause-side fan from one colored ribbon entry to a finite clause
port.  Its first segment is parallel to the advertised source direction. -/
def standardClauseRibbonFan
    (direction : AxisDirection) (color : WireColor)
    (port : Cell) : List Cell :=
  match direction with
  | .east | .west =>
      horizontalFirstElbow
        (standardRibbonMacrocellEntry direction color) port
  | .north | .south | .invalid =>
      verticalFirstElbow
        (standardRibbonMacrocellEntry direction color) port

@[simp]
theorem standardVariableRibbonFan_head?
    (port : Cell) (direction : AxisDirection)
    (color : WireColor) :
    (standardVariableRibbonFan port direction color).head? =
      some port := by
  cases direction <;> simp [standardVariableRibbonFan]

@[simp]
theorem standardVariableRibbonFan_getLast?
    (port : Cell) (direction : AxisDirection)
    (color : WireColor) :
    (standardVariableRibbonFan port direction color).getLast? =
      some (standardRibbonMacrocellExit direction color) := by
  cases direction <;> simp [standardVariableRibbonFan]

@[simp]
theorem standardClauseRibbonFan_head?
    (direction : AxisDirection) (color : WireColor)
    (port : Cell) :
    (standardClauseRibbonFan direction color port).head? =
      some (standardRibbonMacrocellEntry direction color) := by
  cases direction <;> simp [standardClauseRibbonFan]

@[simp]
theorem standardClauseRibbonFan_getLast?
    (direction : AxisDirection) (color : WireColor)
    (port : Cell) :
    (standardClauseRibbonFan direction color port).getLast? =
      some port := by
  cases direction <;> simp [standardClauseRibbonFan]

/-- Every local variable fan is rectilinear. -/
theorem standardVariableRibbonFan_orthogonal
    (port : Cell) (direction : AxisDirection)
    (color : WireColor) :
    OrthogonalPolyline
      (standardVariableRibbonFan port direction color) := by
  cases direction <;>
    simp only [standardVariableRibbonFan] <;>
    first
    | exact verticalFirstElbow_orthogonal _ _
    | exact horizontalFirstElbow_orthogonal _ _

/-- Every local clause fan is rectilinear. -/
theorem standardClauseRibbonFan_orthogonal
    (direction : AxisDirection) (color : WireColor)
    (port : Cell) :
    OrthogonalPolyline
      (standardClauseRibbonFan direction color port) := by
  cases direction <;>
    simp only [standardClauseRibbonFan] <;>
    first
    | exact horizontalFirstElbow_orthogonal _ _
    | exact verticalFirstElbow_orthogonal _ _

/-- A horizontal-first elbow between two points of the standard ribbon
block stays in that block. -/
theorem horizontalFirstElbow_points_bounded
    {source target point : Cell}
    (sourceBounded : InStandardRibbonMacrocell source)
    (targetBounded : InStandardRibbonMacrocell target)
    (member : point ∈ horizontalFirstElbow source target) :
    InStandardRibbonMacrocell point := by
  rcases sourceBounded with
    ⟨sourceXLower, sourceXUpper, sourceYLower, sourceYUpper⟩
  rcases targetBounded with
    ⟨targetXLower, targetXUpper, targetYLower, targetYUpper⟩
  rcases mem_horizontalFirstElbow member with
    pointEq | pointEq | pointEq
  · subst point
    exact
      ⟨sourceXLower, sourceXUpper, sourceYLower, sourceYUpper⟩
  · subst point
    exact
      ⟨targetXLower, targetXUpper, targetYLower, targetYUpper⟩
  · simpa [pointEq, InStandardRibbonMacrocell] using
      And.intro targetXLower
        (And.intro targetXUpper
          (And.intro sourceYLower sourceYUpper))

/-- A vertical-first elbow between two points of the standard ribbon block
stays in that block. -/
theorem verticalFirstElbow_points_bounded
    {source target point : Cell}
    (sourceBounded : InStandardRibbonMacrocell source)
    (targetBounded : InStandardRibbonMacrocell target)
    (member : point ∈ verticalFirstElbow source target) :
    InStandardRibbonMacrocell point := by
  rcases sourceBounded with
    ⟨sourceXLower, sourceXUpper, sourceYLower, sourceYUpper⟩
  rcases targetBounded with
    ⟨targetXLower, targetXUpper, targetYLower, targetYUpper⟩
  rcases mem_verticalFirstElbow member with
    pointEq | pointEq | pointEq
  · subst point
    exact
      ⟨sourceXLower, sourceXUpper, sourceYLower, sourceYUpper⟩
  · subst point
    exact
      ⟨targetXLower, targetXUpper, targetYLower, targetYUpper⟩
  · simpa [pointEq, InStandardRibbonMacrocell] using
      And.intro sourceXLower
        (And.intro sourceXUpper
          (And.intro targetYLower targetYUpper))

/-- Every standard colored ribbon entry lies in the closed standard block. -/
theorem standardRibbonMacrocellEntry_bounded
    (direction : AxisDirection) (color : WireColor) :
    InStandardRibbonMacrocell
      (standardRibbonMacrocellEntry direction color) := by
  cases direction <;> cases color <;>
    native_decide

/-- Every standard colored ribbon exit lies in the closed standard block. -/
theorem standardRibbonMacrocellExit_bounded
    (direction : AxisDirection) (color : WireColor) :
    InStandardRibbonMacrocell
      (standardRibbonMacrocellExit direction color) := by
  cases direction <;> cases color <;>
    native_decide

/-- Exact local variable-gadget port inside its owning refined block. -/
def occurrenceVariableRibbonFanPort
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) : Cell :=
  Cell.add standardThreeStrandLayout.variableOffset
    (routedVariablePortPosition source entry color)

/-- Exact local clause-gadget port inside its owning refined block. -/
def occurrenceClauseRibbonFanPort
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) : Cell :=
  Cell.add standardThreeStrandLayout.clauseOffset
    (routedClausePortPosition source entry color)

/-! ## Finite endpoint bounds -/

/-- Every element position in every one-occurrence variable site lies in
the standard closed ribbon block. -/
theorem all_oneVariableSiteDrawing_elementPositionsInRibbonBlock :
    ∀ kind polarity element,
      InStandardRibbonMacrocell
        (Cell.add standardThreeStrandLayout.variableOffset
          ((oneVariableSiteDrawing kind polarity).elementPosition
            element)) := by
  native_decide

/-- The corresponding finite check for every two-occurrence variable site. -/
theorem all_twoVariableSiteDrawing_elementPositionsInRibbonBlock :
    ∀ firstKind secondKind firstPolarity secondPolarity element,
      InStandardRibbonMacrocell
        (Cell.add standardThreeStrandLayout.variableOffset
          ((twoVariableSiteDrawing firstKind secondKind
            firstPolarity secondPolarity).elementPosition element)) := by
  native_decide

/-- The corresponding finite check for every three-occurrence variable
site. -/
theorem all_threeVariableSiteDrawing_elementPositionsInRibbonBlock :
    ∀ firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity element,
      InStandardRibbonMacrocell
        (Cell.add standardThreeStrandLayout.variableOffset
          ((threeVariableSiteDrawing
            firstKind secondKind thirdKind
            firstPolarity secondPolarity thirdPolarity)
            |>.elementPosition element)) := by
  native_decide

/-- Every element position in an actual finite variable-site drawing lies
in its standard closed ribbon block. -/
theorem sourceVariableSiteDrawing_elementPositionsInRibbonBlock
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source) :
    ∀ element,
      InStandardRibbonMacrocell
        (Cell.add standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source atom).elementPosition
            element)) := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · unfold sourceVariableSiteDrawing sourceVariableSiteCount
      sourceVariableSiteKind sourceVariableSitePolarity
    rw [one]
    exact
      all_oneVariableSiteDrawing_elementPositionsInRibbonBlock
        (occurrenceConnectorKind source atom .first)
        (occurrencePolarity source atom .first)
  · rcases twoOrThree with two | three
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [two]
      exact
        all_twoVariableSiteDrawing_elementPositionsInRibbonBlock
          (occurrenceConnectorKind source atom .first)
          (occurrenceConnectorKind source atom .second)
          (occurrencePolarity source atom .first)
          (occurrencePolarity source atom .second)
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [three]
      exact
        all_threeVariableSiteDrawing_elementPositionsInRibbonBlock
          (occurrenceConnectorKind source atom .first)
          (occurrenceConnectorKind source atom .second)
          (occurrenceConnectorKind source atom .third)
          (occurrencePolarity source atom .first)
          (occurrencePolarity source atom .second)
          (occurrencePolarity source atom .third)

/-- The exact routed variable port lies in its standard ribbon block. -/
theorem occurrenceVariableRibbonFanPort_bounded
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    InStandardRibbonMacrocell
      (occurrenceVariableRibbonFanPort source entry color) := by
  exact
    sourceVariableSiteDrawing_elementPositionsInRibbonBlock
      source entry.1.1 entry.atom_mem
      ((sourceVariableSiteDrawing source entry.1.1).reference
        (routedActiveVariableSiteTriple source entry color) color)

/-- The exact routed clause port lies in its standard ribbon block. -/
theorem occurrenceClauseRibbonFanPort_bounded
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    InStandardRibbonMacrocell
      (occurrenceClauseRibbonFanPort source entry color) := by
  have margin :=
    routedClauseLocalOffset_hasUpperMargin source entry color
  dsimp only at margin
  rcases margin with
    ⟨xLower, xUpper, yLower, yUpper⟩
  unfold occurrenceClauseRibbonFanPort
    InStandardRibbonMacrocell
  exact
    ⟨xLower, by omega, yLower, by omega⟩

/-- Every point of a standard variable fan remains in the standard ribbon
block. -/
theorem standardVariableRibbonFan_points_bounded
    {port point : Cell} {direction : AxisDirection}
    {color : WireColor}
    (portBounded : InStandardRibbonMacrocell port)
    (member :
      point ∈ standardVariableRibbonFan port direction color) :
    InStandardRibbonMacrocell point := by
  cases direction with
  | east | west =>
      exact verticalFirstElbow_points_bounded
        portBounded
        (standardRibbonMacrocellExit_bounded _ color)
        member
  | north | south | invalid =>
      exact horizontalFirstElbow_points_bounded
        portBounded
        (standardRibbonMacrocellExit_bounded _ color)
        member

/-- Every point of a standard clause fan remains in the standard ribbon
block. -/
theorem standardClauseRibbonFan_points_bounded
    {port point : Cell} {direction : AxisDirection}
    {color : WireColor}
    (portBounded : InStandardRibbonMacrocell port)
    (member :
      point ∈ standardClauseRibbonFan direction color port) :
    InStandardRibbonMacrocell point := by
  cases direction with
  | east | west =>
      exact horizontalFirstElbow_points_bounded
        (standardRibbonMacrocellEntry_bounded _ color)
        portBounded member
  | north | south | invalid =>
      exact verticalFirstElbow_points_bounded
        (standardRibbonMacrocellEntry_bounded _ color)
        portBounded member

/-- Translated variable-side fan from the finite gadget port to the first
ribbon macrocell boundary. -/
noncomputable def occurrenceRibbonVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  translatePolyline
    (ribbonMacrocellOrigin (placement.position entry.1.1))
    (standardVariableRibbonFan
      (occurrenceVariableRibbonFanPort source.erase entry color)
      (occurrenceSourceVariableDirection presentation entry)
      color)

/-- Translated clause-side fan from the final ribbon macrocell boundary to
the finite clause terminal in its referenced periodic translate. -/
noncomputable def occurrenceRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  let data := occurrenceSpliceData presentation entry
  let target :=
    PositionedPeriodicCNF.variableToClauseTarget
      placement data.positionedClause data.tagged.1
  translatePolyline
    (ribbonMacrocellOrigin target)
    (standardClauseRibbonFan
      (occurrenceSourceClauseDirection presentation entry)
      color
      (occurrenceClauseRibbonFanPort source.erase entry color))

/-- The translated variable fan has exactly the finite variable port and
the first ribbon-core boundary as its endpoints. -/
theorem occurrenceRibbonVariableStub_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (occurrenceRibbonVariableStub
        presentation entry color).head? =
        some (Cell.add
          (constructedVariableOrigin placement
            standardThreeStrandLayout entry.1.1)
          (routedVariablePortPosition source.erase entry color)) ∧
      (occurrenceRibbonVariableStub
        presentation entry color).getLast? =
        some (ribbonCorridorRouteStart color
          (occurrenceUnitSourceRoute presentation entry)) := by
  constructor
  · simp [occurrenceRibbonVariableStub,
      occurrenceVariableRibbonFanPort,
      PeriodicOrthocrossing.translatePolyline,
      constructedVariableOrigin, ribbonMacrocellOrigin,
      Cell.add]
    all_goals omega
  · rw [occurrenceRibbonCorridorRouteStart_eq
      presentation entry color]
    simp [occurrenceRibbonVariableStub,
      PeriodicOrthocrossing.translatePolyline,
      ribbonMacrocellExit]

/-- The translated clause fan has exactly the final ribbon-core boundary and
the finite translated clause port as its endpoints. -/
theorem occurrenceRibbonClauseStub_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (occurrenceRibbonClauseStub
        presentation entry color).head? =
        some (ribbonCorridorRouteEnd color
          (occurrenceUnitSourceRoute presentation entry)) ∧
      (occurrenceRibbonClauseStub
        presentation entry color).getLast? =
        some (routedClauseTargetPosition source.erase
          (standardThreeStrandLayout.factor * placement.period)
          (constructedClauseOrigin source standardThreeStrandLayout)
          entry color) := by
  let data := occurrenceSpliceData presentation entry
  constructor
  · rw [occurrenceRibbonCorridorRouteEnd_eq
      presentation entry color]
    simp [occurrenceRibbonClauseStub,
      PeriodicOrthocrossing.translatePolyline,
      ribbonMacrocellEntry]
  · rw [standardRoutedClauseTarget_eq_refinedSourceTarget
      presentation entry color]
    simp [occurrenceRibbonClauseStub,
      occurrenceClauseRibbonFanPort,
      PeriodicOrthocrossing.translatePolyline,
      ribbonMacrocellOrigin, Cell.add]
    all_goals omega

/-- Translating the local variable fan preserves rectilinearity. -/
theorem occurrenceRibbonVariableStub_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (occurrenceRibbonVariableStub presentation entry color) := by
  exact
    (standardVariableRibbonFan_orthogonal
      (occurrenceVariableRibbonFanPort source.erase entry color)
      (occurrenceSourceVariableDirection presentation entry)
      color).translate
        (ribbonMacrocellOrigin (placement.position entry.1.1))

/-- Translating the local clause fan preserves rectilinearity. -/
theorem occurrenceRibbonClauseStub_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (occurrenceRibbonClauseStub presentation entry color) := by
  let data := occurrenceSpliceData presentation entry
  exact
    (standardClauseRibbonFan_orthogonal
      (occurrenceSourceClauseDirection presentation entry)
      color
      (occurrenceClauseRibbonFanPort source.erase entry color)).translate
        (ribbonMacrocellOrigin
          (PositionedPeriodicCNF.variableToClauseTarget
            placement data.positionedClause data.tagged.1))

/-- Every translated variable-fan point stays in the source variable's
owning refined block. -/
theorem occurrenceRibbonVariableStub_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (member :
      point ∈ occurrenceRibbonVariableStub
        presentation entry color) :
    InRibbonMacrocell (placement.position entry.1.1) point := by
  unfold occurrenceRibbonVariableStub
    PeriodicOrthocrossing.translatePolyline at member
  rcases List.mem_map.mp member with
    ⟨localPoint, localMember, rfl⟩
  apply inRibbonMacrocell_add_origin
  exact
    standardVariableRibbonFan_points_bounded
      (occurrenceVariableRibbonFanPort_bounded
        source.erase entry color)
      localMember

/-- Every translated clause-fan point stays in the source clause endpoint's
owning refined block. -/
theorem occurrenceRibbonClauseStub_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (member :
      point ∈ occurrenceRibbonClauseStub
        presentation entry color) :
    let data := occurrenceSpliceData presentation entry
    InRibbonMacrocell
      (PositionedPeriodicCNF.variableToClauseTarget
        placement data.positionedClause data.tagged.1)
      point := by
  let data := occurrenceSpliceData presentation entry
  unfold occurrenceRibbonClauseStub
    PeriodicOrthocrossing.translatePolyline at member
  rcases List.mem_map.mp member with
    ⟨localPoint, localMember, rfl⟩
  apply inRibbonMacrocell_add_origin
  exact
    standardClauseRibbonFan_points_bounded
      (occurrenceClauseRibbonFanPort_bounded
        source.erase entry color)
      localMember

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
