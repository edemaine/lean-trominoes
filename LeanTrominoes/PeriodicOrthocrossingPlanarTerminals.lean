import LeanTrominoes.PeriodicOrthocrossingPlanarCore

/-!
# Segment terminals and complete carrier chains

Crossing boundaries alone omit carriers with no crossing and the portions
before the first and after the last crossing.  We therefore add explicit
start and finish variables for every neighboring segment occurrence.  Sorting
these terminals together with the crossing boundaries yields the complete
finite equality chain along each geometric segment.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Which endpoint of a segment occurrence a terminal represents. -/
inductive SegmentEnd
  | start
  | finish
  deriving DecidableEq, Repr

/-- One endpoint variable of one translated indexed segment occurrence. -/
structure SegmentTerminal where
  indexed : IndexedGridSegment
  translate : Cell
  endpoint : SegmentEnd
  deriving DecidableEq, Repr

/-- The segment-occurrence carrier key of a terminal. -/
def SegmentTerminal.carrierKey (terminal : SegmentTerminal) :
    Nat × Nat × Cell :=
  PeriodicGridDrawing.SegmentOccurrenceKey
    terminal.indexed terminal.translate

/-- The translated drawing-grid endpoint named by a terminal. -/
def SegmentTerminal.drawingPoint
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (terminal : SegmentTerminal) : Cell :=
  let translated :=
    terminal.indexed.segment.translate
      ((drawing graph).periodTranslation terminal.translate)
  match terminal.endpoint with
  | .start => translated.start
  | .finish => translated.finish

/-- Macro-grid position of a segment terminal, centered in the endpoint's
`20 × 20` macrocell. -/
def SegmentTerminal.position
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (terminal : SegmentTerminal) : Cell :=
  Cell.add (Cell.scale planarMacroScale (terminal.drawingPoint graph))
    (10, 10)

/-- The two terminals of one indexed segment occurrence. -/
def occurrenceTerminals
    (occurrence : IndexedGridSegment × Cell) :
    List SegmentTerminal :=
  [⟨occurrence.1, occurrence.2, .start⟩,
    ⟨occurrence.1, occurrence.2, .finish⟩]

/-- Every segment terminal in the neighboring `3 × 3` occurrence block. -/
def drawingSegmentTerminals
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List SegmentTerminal :=
  (neighborOccurrences graph).flatMap occurrenceTerminals

/-- External variables occurring along a complete segment carrier. -/
inductive CarrierNode
  | boundary (boundary : CrossingBoundary)
  | terminal (terminal : SegmentTerminal)
  deriving DecidableEq, Repr

/-- Project either kind of carrier node to its translated segment occurrence. -/
def CarrierNode.carrierKey : CarrierNode → Nat × Nat × Cell
  | .boundary crossingBoundary => crossingBoundary.carrierKey
  | .terminal segmentTerminal => segmentTerminal.carrierKey

/-- Macro-grid position of either kind of carrier node. -/
def CarrierNode.position
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : CarrierNode → Cell
  | .boundary crossingBoundary => crossingBoundary.position
  | .terminal segmentTerminal => segmentTerminal.position graph

/-- Whether a carrier node belongs to a horizontal segment.  Boundary sides
determine this directly; terminals inspect their stored segment. -/
def CarrierNode.isHorizontal : CarrierNode → Bool
  | .boundary ⟨_, .left⟩
  | .boundary ⟨_, .right⟩ => true
  | .boundary ⟨_, .top⟩
  | .boundary ⟨_, .bottom⟩ => false
  | .terminal segmentTerminal =>
      decide segmentTerminal.indexed.segment.IsHorizontal

/-- Order coordinate of a complete carrier node in the macro-grid. -/
def CarrierNode.orderCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) : Int :=
  if node.isHorizontal then
    (node.position graph).1
  else
    (node.position graph).2

/-- All segment terminals and crossing boundaries before grouping by key. -/
def drawingCarrierNodes
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CarrierNode :=
  (drawingSegmentTerminals graph).map CarrierNode.terminal ++
    (drawingCrossingBoundaries graph).map CarrierNode.boundary

/-- All nodes belonging to one translated segment occurrence, sorted along
its geometric axis. -/
def completeCarrierNodes
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    List CarrierNode :=
  ((drawingCarrierNodes graph).filter fun node =>
    node.carrierKey = key).insertionSort fun first second =>
      first.orderCoordinate graph ≤ second.orderCoordinate graph

@[simp]
theorem mem_completeCarrierNodes_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell) (node : CarrierNode) :
    node ∈ completeCarrierNodes graph key ↔
      node ∈ drawingCarrierNodes graph ∧ node.carrierKey = key := by
  simp [completeCarrierNodes]

/-- Whether a pair consists of the two boundary ports of the same crossover
site.  Their equality is already enforced inside the crossover gadget. -/
def CarrierNode.sameCrossoverSite
    (first second : CarrierNode) : Bool :=
  match first, second with
  | .boundary first, .boundary second =>
      decide (first.crossing = second.crossing)
  | _, _ => false

/-- Two clause positions between a pair of consecutive complete carrier
nodes. -/
def carrierNodeEqualityPositions
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : CarrierNode) : EqualityPositions :=
  let firstPosition := first.position graph
  let secondPosition := second.position graph
  if first.isHorizontal then
    let step : Int := if firstPosition.1 ≤ secondPosition.1 then 1 else -1
    ⟨Cell.add firstPosition (3 * step, 0),
      Cell.add firstPosition (6 * step, 0)⟩
  else
    let step : Int := if firstPosition.2 ≤ secondPosition.2 then 1 else -1
    ⟨Cell.add firstPosition (0, 3 * step),
      Cell.add firstPosition (0, 6 * step)⟩

/-- Convert a consecutive complete-carrier pair to a positioned equality
link. -/
def carrierNodePairLink
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (pair : CarrierNode × CarrierNode) :
    EqualityLink CarrierNode where
  first := pair.1
  second := pair.2
  positions := carrierNodeEqualityPositions graph pair.1 pair.2

/-- The complete equality chain along one translated segment occurrence,
omitting only the pair internal to a crossover site. -/
def completeCarrierLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    List (EqualityLink CarrierNode) :=
  ((consecutivePairs (completeCarrierNodes graph key)).filter fun pair =>
    !pair.1.sameCrossoverSite pair.2).map
      (carrierNodePairLink graph)

/-- Every complete-carrier link stays on its requested occurrence key. -/
theorem completeCarrierLinks_common_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ completeCarrierLinks graph key) :
    link.first.carrierKey = key ∧
      link.second.carrierKey = key := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have pairMem' := (List.mem_filter.mp pairMem).1
  have members := mem_of_mem_consecutivePairs pairMem'
  exact
    ⟨(mem_completeCarrierNodes_iff graph key pair.1).mp members.1 |>.2,
      (mem_completeCarrierNodes_iff graph key pair.2).mp members.2 |>.2⟩

/-- Every carrier key represented by either a terminal or a crossing
boundary. -/
def drawingCompleteCarrierKeys
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  ((drawingCarrierNodes graph).map CarrierNode.carrierKey).dedup

/-- All complete segment-carrier equality links in the neighboring block. -/
def drawingCompleteCarrierLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EqualityLink CarrierNode) :=
  (drawingCompleteCarrierKeys graph).flatMap fun key =>
    completeCarrierLinks graph key

/-- Every complete drawing-carrier link stays on one occurrence key. -/
theorem drawingCompleteCarrierLinks_common_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    link.first.carrierKey = link.second.carrierKey := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, keyMem, linkMem⟩
  have common := completeCarrierLinks_common_key graph key linkMem
  exact common.1.trans common.2.symm

/-- Positioned equality clauses along every complete segment carrier. -/
def drawingCompleteCarrierFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause CarrierNode) :=
  equalityFamily (drawingCompleteCarrierLinks graph)

/-- Any segment-occurrence assignment satisfies the complete carrier chains. -/
theorem drawingCompleteCarrierFormula_holds
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : (Nat × Nat × Cell) → Bool) :
    FormulaHolds (assignment ∘ CarrierNode.carrierKey)
      (drawingCompleteCarrierFormula graph) := by
  apply equalityFamily_holds_of_common_key
    CarrierNode.carrierKey assignment (drawingCompleteCarrierLinks graph)
  intro link linkMem
  exact drawingCompleteCarrierLinks_common_key graph linkMem

end PeriodicOrthocrossing
end LeanTrominoes
