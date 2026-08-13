/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarCrossovers
import LeanTrominoes.PlanarThreeSATWires
import Mathlib.Data.List.Sort

/-!
# Wire links between drawing crossovers

Every crossover boundary belongs to one translated segment occurrence.  We
group the finite boundary list by this carrier key, sort horizontal ports by
their `x` coordinate and vertical ports by `y`, and connect consecutive ports
belonging to distinct crossover sites by positioned equality links.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The local Figure 8 position of a crossover boundary variable. -/
def CrossingSide.localPosition : CrossingSide → Cell
  | .left => CrossoverVariable.position .aLeft
  | .right => CrossoverVariable.position .aRight
  | .top => CrossoverVariable.position .bTop
  | .bottom => CrossoverVariable.position .bBottom

/-- Absolute macro-grid position of a crossover boundary variable. -/
def CrossingBoundary.position (boundary : CrossingBoundary) : Cell :=
  Cell.add (crossingMacroOrigin boundary.crossing)
    boundary.side.localPosition

/-- All four boundary variables at every canonical crossing site. -/
def drawingCrossingBoundaries
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingBoundary :=
  (orientedCrossings graph).flatMap fun crossing =>
    [⟨crossing, .left⟩, ⟨crossing, .right⟩,
      ⟨crossing, .top⟩, ⟨crossing, .bottom⟩]

/-- Integer order coordinate along the boundary's carrier axis.  Doubling
the crossing coordinate and using a side bit orders the two ports at one
site consecutively. -/
def CrossingBoundary.orderCoordinate (boundary : CrossingBoundary) : Int :=
  match boundary.side with
  | .left => 2 * boundary.crossing.point.1
  | .right => 2 * boundary.crossing.point.1 + 1
  | .top => 2 * boundary.crossing.point.2
  | .bottom => 2 * boundary.crossing.point.2 + 1

/-- All crossing boundaries belonging to one translated segment occurrence,
sorted along that occurrence's axis. -/
def carrierBoundaries
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    List CrossingBoundary :=
  ((drawingCrossingBoundaries graph).filter fun boundary =>
    boundary.carrierKey = key).insertionSort fun first second =>
      first.orderCoordinate ≤ second.orderCoordinate

@[simp]
theorem mem_carrierBoundaries_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell) (boundary : CrossingBoundary) :
    boundary ∈ carrierBoundaries graph key ↔
      boundary ∈ drawingCrossingBoundaries graph ∧
        boundary.carrierKey = key := by
  simp [carrierBoundaries]

/-- Adjacent pairs of a list, without a wraparound pair. -/
def consecutivePairs {α : Type*} : List α → List (α × α)
  | first :: second :: rest =>
      (first, second) :: consecutivePairs (second :: rest)
  | _ => []

/-- Both components of a consecutive pair occur in the source list. -/
theorem mem_of_mem_consecutivePairs
    {α : Type*} {pair : α × α} {items : List α}
    (pairMem : pair ∈ consecutivePairs items) :
    pair.1 ∈ items ∧ pair.2 ∈ items := by
  induction items with
  | nil =>
      simp [consecutivePairs] at pairMem
  | cons first rest induction =>
      cases rest with
      | nil =>
          simp [consecutivePairs] at pairMem
      | cons second rest =>
          simp only [consecutivePairs, List.mem_cons] at pairMem
          rcases pairMem with pairEq | pairMem
          · subst pair
            simp
          · have members := induction pairMem
            exact ⟨by simp [members.1], by simp [members.2]⟩

/-- Clause positions a short distance from the first endpoint, along the
carrier axis.  Consecutive distinct macrocells leave enough room for these
two binary clauses. -/
def wireEqualityPositions
    (first second : CrossingBoundary) : EqualityPositions :=
  let firstPosition := first.position
  let secondPosition := second.position
  match first.side with
  | .left | .right =>
      let step : Int := if firstPosition.1 ≤ secondPosition.1 then 1 else -1
      ⟨Cell.add firstPosition (3 * step, 0),
        Cell.add firstPosition (6 * step, 0)⟩
  | .top | .bottom =>
      let step : Int := if firstPosition.2 ≤ secondPosition.2 then 1 else -1
      ⟨Cell.add firstPosition (0, 3 * step),
        Cell.add firstPosition (0, 6 * step)⟩

/-- Convert a consecutive carrier-boundary pair into an equality link. -/
def carrierPairLink (pair : CrossingBoundary × CrossingBoundary) :
    EqualityLink CrossingBoundary where
  first := pair.1
  second := pair.2
  positions := wireEqualityPositions pair.1 pair.2

/-- Equality links between consecutive ports of distinct crossover sites on
one segment-occurrence carrier. -/
def carrierWireLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    List (EqualityLink CrossingBoundary) :=
  ((consecutivePairs (carrierBoundaries graph key)).filter fun pair =>
    pair.1.crossing ≠ pair.2.crossing).map carrierPairLink

/-- Every carrier link joins two boundary variables with the requested
carrier key. -/
theorem carrierWireLinks_common_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell)
    {link : EqualityLink CrossingBoundary}
    (linkMem : link ∈ carrierWireLinks graph key) :
    link.first.carrierKey = key ∧
      link.second.carrierKey = key := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have pairMem' := (List.mem_filter.mp pairMem).1
  have members := mem_of_mem_consecutivePairs pairMem'
  exact ⟨(mem_carrierBoundaries_iff graph key pair.1).mp members.1 |>.2,
    (mem_carrierBoundaries_iff graph key pair.2).mp members.2 |>.2⟩

/-- The finite carrier keys that actually occur at canonical crossings. -/
def drawingCrossingCarrierKeys
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  ((drawingCrossingBoundaries graph).map
    CrossingBoundary.carrierKey).dedup

/-- All equality links between consecutive crossover sites in the
fundamental square. -/
def drawingWireLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EqualityLink CrossingBoundary) :=
  (drawingCrossingCarrierKeys graph).flatMap fun key =>
    carrierWireLinks graph key

/-- Every drawing wire link stays on one translated segment occurrence. -/
theorem drawingWireLinks_common_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CrossingBoundary}
    (linkMem : link ∈ drawingWireLinks graph) :
    link.first.carrierKey = link.second.carrierKey := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, keyMem, linkMem⟩
  have common := carrierWireLinks_common_key graph key linkMem
  exact common.1.trans common.2.symm

/-- The positioned equality clauses joining consecutive crossover sites. -/
def drawingWireFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause CrossingBoundary) :=
  equalityFamily (drawingWireLinks graph)

/-- Any segment-occurrence assignment satisfies every drawing wire link. -/
theorem drawingWireFormula_holds_carrierBoundaryAssignment
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : (Nat × Nat × Cell) → Bool) :
    FormulaHolds (carrierBoundaryAssignment assignment)
      (drawingWireFormula graph) := by
  apply equalityFamily_holds_of_common_key
    CrossingBoundary.carrierKey assignment (drawingWireLinks graph)
  intro link linkMem
  exact drawingWireLinks_common_key graph linkMem

end PeriodicOrthocrossing
end LeanTrominoes
