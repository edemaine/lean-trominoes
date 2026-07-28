import LeanTrominoes.PeriodicOrthocrossingPlanarSATMacrocellBounds
import LeanTrominoes.PeriodicOrthocrossingCarrierTranslationCore

/-!
# Period translations of planar-SAT clause sources

The finite planar-SAT drawing represents a bounded collection of physical
occurrences of five local gadget families.  Reindexing a periodic occurrence
requires translating the complete source data, not just its route points.
This file defines that common action on route bends, routed vertex sites,
external planar-SAT nodes, clause sources, and source components.

The basic geometry lemmas show that one lattice shift adds exactly the
physical drawing-period translation to every drawing-grid center, and the
corresponding refined macro-period translation to every gadget origin.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Translate a route bend to the same bend in another route occurrence. -/
def RouteBend.periodTranslate
    (routeBend : RouteBend) (shift : Cell) : RouteBend where
  routeIndex := routeBend.routeIndex
  incomingSegmentIndex := routeBend.incomingSegmentIndex
  translate := Cell.add routeBend.translate shift
  incomingStart := routeBend.incomingStart
  bend := routeBend.bend
  outgoingFinish := routeBend.outgoingFinish

/-- Translate a lifted routed-clause site by a drawing-period shift. -/
def clauseRouteSitePeriodTranslate
    (site : ClauseRouteSite) (shift : Cell) : ClauseRouteSite :=
  (site.1, Cell.add site.2 shift)

/-- Translate a lifted routed-variable site by a drawing-period shift. -/
def variableRouteSitePeriodTranslate
    {Variable : Type*}
    (site : VariableRouteSite Variable) (shift : Cell) :
    VariableRouteSite Variable :=
  (site.1, Cell.add site.2 shift)

/-- Translate an external planar-SAT node to the corresponding physical
occurrence. -/
def PlanarSATNode.periodTranslate
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : PlanarSATNode Variable) (shift : Cell) :
    PlanarSATNode Variable := by
  cases node with
  | carrier carrier =>
      exact .carrier (carrier.periodTranslate graph shift)
  | atom site =>
      exact .atom (variableRouteSitePeriodTranslate site shift)

/-- Translate both endpoints and both clause positions of an equality link
between external planar-SAT nodes. -/
def planarSATNodeLinkPeriodTranslate
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink (PlanarSATNode Variable))
    (shift : Cell) :
    EqualityLink (PlanarSATNode Variable) where
  first := link.first.periodTranslate graph shift
  second := link.second.periodTranslate graph shift
  positions := EqualityPositions.periodTranslate link.positions
    (carrierMacroPeriodTranslation graph shift)

namespace DrawingPlanarSATComponent

/-- Translate the complete physical data of one local planar-SAT component. -/
def periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (component : DrawingPlanarSATComponent Variable)
    (shift : Cell) :
    DrawingPlanarSATComponent Variable :=
  let graph := PeriodicCNF.incidenceGraph formula
  match component with
  | .crossover crossing =>
      .crossover (crossing.periodTranslate graph shift)
  | .carrier link =>
      .carrier (carrierLinkPeriodTranslate graph link shift)
  | .bend routeBend =>
      .bend (routeBend.periodTranslate shift)
  | .routedClause site =>
      .routedClause (clauseRouteSitePeriodTranslate site shift)
  | .routedVariable site arm link =>
      .routedVariable
        (variableRouteSitePeriodTranslate site shift)
        arm
        (planarSATNodeLinkPeriodTranslate graph link shift)

end DrawingPlanarSATComponent

namespace DrawingPlanarSATClauseSource

/-- Translate a clause source without changing its index inside the local
gadget drawing. -/
def periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell) :
    DrawingPlanarSATClauseSource Variable :=
  let graph := PeriodicCNF.incidenceGraph formula
  match source with
  | .crossover crossing localClauseIndex =>
      .crossover
        (crossing.periodTranslate graph shift)
        localClauseIndex
  | .carrier link localClauseIndex =>
      .carrier
        (carrierLinkPeriodTranslate graph link shift)
        localClauseIndex
  | .bend routeBend localClauseIndex =>
      .bend
        (routeBend.periodTranslate shift)
        localClauseIndex
  | .routedClause site =>
      .routedClause
        (clauseRouteSitePeriodTranslate site shift)
  | .routedVariable site armIndex arm link localClauseIndex =>
      .routedVariable
        (variableRouteSitePeriodTranslate site shift)
        armIndex arm
        (planarSATNodeLinkPeriodTranslate graph link shift)
        localClauseIndex

@[simp]
theorem localClauseIndex_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell) :
    (source.periodTranslate formula shift).localClauseIndex =
      source.localClauseIndex := by
  cases source <;> rfl

@[simp]
theorem component_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell) :
    (source.periodTranslate formula shift).component =
      source.component.periodTranslate formula shift := by
  cases source <;> rfl

end DrawingPlanarSATClauseSource

/-- Period translation is additive on drawing-grid lattice vectors. -/
theorem periodTranslation_add
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : Cell) :
    (drawing graph).periodTranslation (Cell.add first second) =
      Cell.add ((drawing graph).periodTranslation first)
        ((drawing graph).periodTranslation second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale]
  constructor <;> ring

/-- Refined macro-period translation is the macro-scale image of the
underlying drawing-period translation. -/
theorem carrierMacroPeriodTranslation_eq_scale_periodTranslation
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (shift : Cell) :
    carrierMacroPeriodTranslation graph shift =
      Cell.scale planarMacroScale
        ((drawing graph).periodTranslation shift) := by
  rcases shift with ⟨shiftX, shiftY⟩
  simp [carrierMacroPeriodTranslation,
    PeriodicGridDrawing.periodTranslation,
    drawingGridSize, Cell.scale]
  constructor <;> ring

@[simp]
theorem RouteBend.drawingPoint_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend) (shift : Cell) :
    (routeBend.periodTranslate shift).drawingPoint graph =
      Cell.add (routeBend.drawingPoint graph)
        ((drawing graph).periodTranslation shift) := by
  simp [RouteBend.periodTranslate, RouteBend.drawingPoint,
    periodTranslation_add]
  rcases (drawing graph).periodTranslation routeBend.translate with
    ⟨translateX, translateY⟩
  rcases (drawing graph).periodTranslation shift with
    ⟨shiftX, shiftY⟩
  rcases routeBend.bend with ⟨bendX, bendY⟩
  simp [Cell.add]
  constructor <;> ring

theorem liftedIncidenceVertexPosition_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (vertex : CNFVertex Variable)
    (translate shift : Cell) :
    liftedIncidenceVertexPosition formula vertex
        (Cell.add translate shift) =
      Cell.add
        (liftedIncidenceVertexPosition formula vertex translate)
        ((drawing (PeriodicCNF.incidenceGraph formula)).periodTranslation
          shift) := by
  simp [liftedIncidenceVertexPosition, periodTranslation_add]
  rcases
      PeriodicGridDrawing.vertexPosition
        (PeriodicCNF.incidenceGraph formula)
        (drawing (PeriodicCNF.incidenceGraph formula)) vertex with
    ⟨vertexX, vertexY⟩
  rcases
      (drawing (PeriodicCNF.incidenceGraph formula)).periodTranslation
        translate with
    ⟨translateX, translateY⟩
  rcases
      (drawing (PeriodicCNF.incidenceGraph formula)).periodTranslation
        shift with
    ⟨shiftX, shiftY⟩
  simp [Cell.add]
  constructor <;> ring

theorem liftedIncidenceVertexMacroOrigin_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (vertex : CNFVertex Variable)
    (translate shift : Cell) :
    liftedIncidenceVertexMacroOrigin formula vertex
        (Cell.add translate shift) =
      Cell.add
        (liftedIncidenceVertexMacroOrigin formula vertex translate)
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift) := by
  unfold liftedIncidenceVertexMacroOrigin
  rw [liftedIncidenceVertexPosition_periodTranslate,
    carrierMacroPeriodTranslation_eq_scale_periodTranslation]
  rcases liftedIncidenceVertexPosition formula vertex translate with
    ⟨vertexX, vertexY⟩
  rcases
      (drawing (PeriodicCNF.incidenceGraph formula)).periodTranslation
        shift with
    ⟨shiftX, shiftY⟩
  simp [Cell.add, Cell.scale]
  constructor <;> ring

@[simp]
theorem routedClauseOrigin_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) (shift : Cell) :
    routedClauseOrigin formula
        (clauseRouteSitePeriodTranslate site shift) =
      Cell.add (routedClauseOrigin formula site)
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift) := by
  exact liftedIncidenceVertexMacroOrigin_periodTranslate
    formula (.clause site.1) site.2 shift

@[simp]
theorem routedVariableOrigin_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) (shift : Cell) :
    routedVariableOrigin formula
        (variableRouteSitePeriodTranslate site shift) =
      Cell.add (routedVariableOrigin formula site)
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift) := by
  exact liftedIncidenceVertexMacroOrigin_periodTranslate
    formula (.variable site.1) site.2 shift

@[simp]
theorem DrawingPlanarSATComponent.macrocellCenter_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (component : DrawingPlanarSATComponent Variable)
    (shift : Cell) :
    (component.periodTranslate formula shift).macrocellCenter formula =
      (component.macrocellCenter formula).map (fun center =>
        Cell.add center
          ((drawing (PeriodicCNF.incidenceGraph formula)).periodTranslation
            shift)) := by
  cases component with
  | crossover crossing =>
      simp [DrawingPlanarSATComponent.periodTranslate,
        DrawingPlanarSATComponent.macrocellCenter,
        CrossingRecord.periodTranslate]
  | carrier link =>
      rfl
  | bend routeBend =>
      simp [DrawingPlanarSATComponent.periodTranslate,
        DrawingPlanarSATComponent.macrocellCenter]
  | routedClause site =>
      simp [DrawingPlanarSATComponent.periodTranslate,
        DrawingPlanarSATComponent.macrocellCenter,
        clauseRouteSitePeriodTranslate,
        liftedIncidenceVertexPosition_periodTranslate]
  | routedVariable site arm link =>
      simp [DrawingPlanarSATComponent.periodTranslate,
        DrawingPlanarSATComponent.macrocellCenter,
        variableRouteSitePeriodTranslate,
        liftedIncidenceVertexPosition_periodTranslate]

end PeriodicOrthocrossing
end LeanTrominoes
