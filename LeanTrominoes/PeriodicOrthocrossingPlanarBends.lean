import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals

/-!
# Equality links through route bends

The complete carrier chains propagate a value along each straight segment
occurrence.  Consecutive segments of one polyline still have distinct
terminal variables, however.  This file records every bend of every
neighboring route occurrence and joins its incoming and outgoing terminals
by one positioned equality link.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Satisfaction distributes over concatenation of embedded clause lists. -/
theorem formulaHolds_route_append_iff
    {Variable : Type*}
    (assignment : Variable → Bool)
    (first second : List (EmbeddedClause Variable)) :
    FormulaHolds assignment (first ++ second) ↔
      FormulaHolds assignment first ∧
        FormulaHolds assignment second := by
  unfold FormulaHolds
  constructor
  · intro holds
    constructor
    · intro clause clauseMem
      exact holds clause (List.mem_append_left second clauseMem)
    · intro clause clauseMem
      exact holds clause (List.mem_append_right first clauseMem)
  · rintro ⟨firstHolds, secondHolds⟩ clause clauseMem
    rcases List.mem_append.mp clauseMem with clauseMem | clauseMem
    · exact firstHolds clause clauseMem
    · exact secondHolds clause clauseMem

/-- A route occurrence is determined by its route index and periodic
translation; its individual segment index is deliberately forgotten. -/
abbrev RouteOccurrenceKey := Nat × Cell

/-- Forget the segment index in a segment-occurrence carrier key. -/
def segmentCarrierRouteKey (key : Nat × Nat × Cell) :
    RouteOccurrenceKey :=
  (key.1, key.2.2)

/-- The route occurrence containing a segment terminal. -/
def SegmentTerminal.routeKey (terminal : SegmentTerminal) :
    RouteOccurrenceKey :=
  (terminal.indexed.routeIndex, terminal.translate)

/-- The route occurrence containing either kind of carrier node. -/
def CarrierNode.routeKey (node : CarrierNode) : RouteOccurrenceKey :=
  segmentCarrierRouteKey node.carrierKey

@[simp]
theorem SegmentTerminal.routeKey_eq_carrierKey
    (terminal : SegmentTerminal) :
    terminal.routeKey = segmentCarrierRouteKey terminal.carrierKey := by
  rfl

/-- Syntactic data for two consecutive segments of one translated route. -/
structure RouteBend where
  routeIndex : Nat
  incomingSegmentIndex : Nat
  translate : Cell
  incomingStart : Cell
  bend : Cell
  outgoingFinish : Cell
  deriving DecidableEq, Repr

/-- Terminal at the end of a bend's incoming segment. -/
def RouteBend.incomingTerminal (routeBend : RouteBend) :
    SegmentTerminal where
  indexed :=
    ⟨routeBend.routeIndex, routeBend.incomingSegmentIndex,
      ⟨routeBend.incomingStart, routeBend.bend⟩⟩
  translate := routeBend.translate
  endpoint := .finish

/-- Terminal at the start of a bend's outgoing segment. -/
def RouteBend.outgoingTerminal (routeBend : RouteBend) :
    SegmentTerminal where
  indexed :=
    ⟨routeBend.routeIndex, routeBend.incomingSegmentIndex + 1,
      ⟨routeBend.bend, routeBend.outgoingFinish⟩⟩
  translate := routeBend.translate
  endpoint := .start

/-- The route occurrence shared by both sides of a bend. -/
def RouteBend.routeKey (routeBend : RouteBend) : RouteOccurrenceKey :=
  (routeBend.routeIndex, routeBend.translate)

@[simp]
theorem RouteBend.incomingTerminal_routeKey (routeBend : RouteBend) :
    routeBend.incomingTerminal.routeKey = routeBend.routeKey := by
  rfl

@[simp]
theorem RouteBend.outgoingTerminal_routeKey (routeBend : RouteBend) :
    routeBend.outgoingTerminal.routeKey = routeBend.routeKey := by
  rfl

/-- The translated drawing point at which a route bends. -/
def RouteBend.drawingPoint
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) : Cell :=
  Cell.add ((drawing graph).periodTranslation routeBend.translate)
    routeBend.bend

@[simp]
theorem RouteBend.incomingTerminal_drawingPoint
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    routeBend.incomingTerminal.drawingPoint graph =
      routeBend.drawingPoint graph := by
  rfl

@[simp]
theorem RouteBend.outgoingTerminal_drawingPoint
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    routeBend.outgoingTerminal.drawingPoint graph =
      routeBend.drawingPoint graph := by
  rfl

/-- Consecutive triples of route points, tagged by the incoming segment
index. -/
def routeBendsAux (routeIndex : Nat) (translate : Cell) :
    Nat → List Cell → List RouteBend
  | incomingSegmentIndex, incomingStart :: bend :: outgoingFinish :: rest =>
      ⟨routeIndex, incomingSegmentIndex, translate,
        incomingStart, bend, outgoingFinish⟩ ::
      routeBendsAux routeIndex translate (incomingSegmentIndex + 1)
        (bend :: outgoingFinish :: rest)
  | _, _ => []

/-- All bends of one translated route occurrence. -/
def routeBends (routeIndex : Nat) (translate : Cell)
    (route : List Cell) : List RouteBend :=
  routeBendsAux routeIndex translate 0 route

/-- All bends in the neighboring `3 × 3` route-occurrence block. -/
def drawingRouteBends
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List RouteBend :=
  (drawing graph).edgeRoutes.zipIdx.flatMap fun taggedRoute =>
    neighborTranslations.flatMap fun translate =>
      routeBends taggedRoute.2 translate taggedRoute.1

/-- Clause positions within the macrocell surrounding a bend. -/
def routeBendEqualityPositions
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend) : EqualityPositions :=
  let origin :=
    Cell.scale planarMacroScale (routeBend.drawingPoint graph)
  ⟨Cell.add origin (8, 8), Cell.add origin (12, 12)⟩

/-- The equality link joining the two segment terminals at one route bend. -/
def RouteBend.equalityLink
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    EqualityLink CarrierNode where
  first := .terminal routeBend.incomingTerminal
  second := .terminal routeBend.outgoingTerminal
  positions := routeBendEqualityPositions graph routeBend

@[simp]
theorem RouteBend.equalityLink_common_route
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    (routeBend.equalityLink graph).first.routeKey =
      (routeBend.equalityLink graph).second.routeKey := by
  rfl

/-- Equality links through every enumerated route bend. -/
def drawingRouteBendLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EqualityLink CarrierNode) :=
  (drawingRouteBends graph).dedup.map fun routeBend =>
    routeBend.equalityLink graph

/-- Every bend link stays within one translated route occurrence. -/
theorem drawingRouteBendLinks_common_route
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingRouteBendLinks graph) :
    link.first.routeKey = link.second.routeKey := by
  rcases List.mem_map.mp linkMem with
    ⟨routeBend, routeBendMem, linkEq⟩
  subst link
  exact routeBend.equalityLink_common_route graph

/-- Positioned equality clauses through every route bend. -/
def drawingRouteBendFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause CarrierNode) :=
  equalityFamily (drawingRouteBendLinks graph)

/-- Any route-occurrence assignment satisfies every bend link. -/
theorem drawingRouteBendFormula_holds
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : RouteOccurrenceKey → Bool) :
    FormulaHolds (assignment ∘ CarrierNode.routeKey)
      (drawingRouteBendFormula graph) := by
  apply equalityFamily_holds_of_common_key
    CarrierNode.routeKey assignment (drawingRouteBendLinks graph)
  intro link linkMem
  exact drawingRouteBendLinks_common_route graph linkMem

/-- Complete straight-segment chains followed by all bend links. -/
def drawingRouteWireFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause CarrierNode) :=
  drawingCompleteCarrierFormula graph ++
    drawingRouteBendFormula graph

/-- A single value per translated route occurrence satisfies the complete
wire formula, through both crossings and bends. -/
theorem drawingRouteWireFormula_holds
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : RouteOccurrenceKey → Bool) :
    FormulaHolds (assignment ∘ CarrierNode.routeKey)
      (drawingRouteWireFormula graph) := by
  rw [drawingRouteWireFormula, formulaHolds_route_append_iff]
  constructor
  · simpa [CarrierNode.routeKey, SegmentTerminal.routeKey,
      segmentCarrierRouteKey, Function.comp_def] using
      drawingCompleteCarrierFormula_holds graph
        (assignment ∘ segmentCarrierRouteKey)
  · exact drawingRouteBendFormula_holds graph assignment

end PeriodicOrthocrossing
end LeanTrominoes
