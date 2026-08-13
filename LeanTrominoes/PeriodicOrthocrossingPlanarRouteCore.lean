/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarBends

/-!
# Complete crossover-and-route planarization core

The first planar core connected only crossover boundary variables.  The
complete route layer has the larger external type `CarrierNode`, containing
both crossing boundaries and segment terminals.  This file instantiates the
crossover family directly with boundary nodes, scopes the complete route
formula into the external summand, and proves the combined semantic
interface.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Crossover ports expressed in the complete carrier-node variable type. -/
def carrierNodeCrossingPorts (crossing : CrossingRecord) :
    CrossoverPorts CarrierNode where
  aLeft := .boundary ⟨crossing, .left⟩
  aRight := .boundary ⟨crossing, .right⟩
  bTop := .boundary ⟨crossing, .top⟩
  bBottom := .boundary ⟨crossing, .bottom⟩

/-- All crossover gadgets, with their external variables embedded into
`CarrierNode`. -/
def drawingCarrierNodeCrossoverFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))) :=
  crossoverFamily (orientedCrossingHalo graph)
    carrierNodeCrossingPorts crossingMacroOrigin 1

/-- Scope every complete route-wire variable into the external summand used
by the crossover family. -/
def scopedDrawingRouteWireFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))) :=
  (drawingRouteWireFormula graph).map fun clause =>
    clause.rename fun node =>
      (Sum.inl node :
        Sum CarrierNode (CrossingRecord × CrossoverInternal))

@[simp]
theorem scopedDrawingRouteWireFormula_holds_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool) :
    FormulaHolds assignment (scopedDrawingRouteWireFormula graph) ↔
      FormulaHolds (assignment ∘ Sum.inl)
        (drawingRouteWireFormula graph) := by
  exact formulaHolds_map assignment
    (fun node =>
      (Sum.inl node :
        Sum CarrierNode (CrossingRecord × CrossoverInternal)))
    id (drawingRouteWireFormula graph)

/-- The complete local planar core: every canonical crossover, every straight
carrier chain, and every route-bend equality. -/
def drawingRoutePlanarCoreFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))) :=
  drawingCarrierNodeCrossoverFormula graph ++
    scopedDrawingRouteWireFormula graph

/-- Satisfaction of the complete core splits into its crossover and route
wire components. -/
theorem drawingRoutePlanarCoreFormula_holds_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool) :
    FormulaHolds assignment (drawingRoutePlanarCoreFormula graph) ↔
      FormulaHolds assignment
          (drawingCarrierNodeCrossoverFormula graph) ∧
        FormulaHolds (assignment ∘ Sum.inl)
          (drawingRouteWireFormula graph) := by
  rw [drawingRoutePlanarCoreFormula,
    formulaHolds_route_append_iff,
    scopedDrawingRouteWireFormula_holds_iff]

/-- The canonical complete-core assignment determined by the two route
signals crossing at each site.  Its internal values depend only on those
signals, so periodic copies of the same physical crossover agree. -/
noncomputable def canonicalRoutePlanarCoreAssignment
    (routeAssignment : RouteOccurrenceKey → Bool) :
    Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool
  | .inl node => routeAssignment node.routeKey
  | .inr (crossing, internal) =>
      canonicalCrossoverAssignment
        (routeAssignment
          (CarrierNode.boundary
            ⟨crossing, .left⟩).routeKey)
        (routeAssignment
          (CarrierNode.boundary
            ⟨crossing, .top⟩).routeKey)
        internal.toVariable

/-- The canonical complete-core assignment satisfies every crossover and
route-wire clause. -/
theorem canonicalRoutePlanarCoreAssignment_holds
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeAssignment : RouteOccurrenceKey → Bool) :
    FormulaHolds
      (canonicalRoutePlanarCoreAssignment routeAssignment)
      (drawingRoutePlanarCoreFormula graph) := by
  apply
    (drawingRoutePlanarCoreFormula_holds_iff graph
      (canonicalRoutePlanarCoreAssignment routeAssignment)).mpr
  constructor
  · apply
      (crossoverFamily_holds_iff
        (canonicalRoutePlanarCoreAssignment routeAssignment)
        (orientedCrossingHalo graph)
        carrierNodeCrossingPorts crossingMacroOrigin 1).mpr
    intro crossing crossingMem
    have canonicalHolds :=
      canonicalCrossoverAssignment_holds
        (routeAssignment
          (CarrierNode.boundary
            ⟨crossing, .left⟩).routeKey)
        (routeAssignment
          (CarrierNode.boundary
            ⟨crossing, .top⟩).routeKey)
    suffices
        canonicalRoutePlanarCoreAssignment routeAssignment ∘
            scopedCrossoverVariableMap crossing
              (carrierNodeCrossingPorts crossing) =
          canonicalCrossoverAssignment
            (routeAssignment
              (CarrierNode.boundary
                ⟨crossing, .left⟩).routeKey)
            (routeAssignment
              (CarrierNode.boundary
                ⟨crossing, .top⟩).routeKey) by
      rw [this]
      exact canonicalHolds
    funext input
    cases input <;> simp [
        canonicalRoutePlanarCoreAssignment,
        scopedCrossoverVariableMap,
        carrierNodeCrossingPorts,
        CrossoverInternal.toVariable,
        CrossingBoundary.carrierKey,
        CarrierNode.routeKey,
        CarrierNode.carrierKey,
        segmentCarrierRouteKey]
  · have routeHolds :=
      drawingRouteWireFormula_holds graph routeAssignment
    have restriction :
        canonicalRoutePlanarCoreAssignment routeAssignment ∘ Sum.inl =
          routeAssignment ∘ CarrierNode.routeKey := by
      funext node
      rfl
    rw [restriction]
    exact routeHolds

/-- Every value assignment to translated routes extends through all complete
wires and all fresh crossover internals, while retaining the requested value
at every carrier node. -/
theorem exists_drawingRoutePlanarCoreFormula_holds_of_routeAssignment
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeAssignment : RouteOccurrenceKey → Bool) :
    ∃ assignment :
        Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool,
      FormulaHolds assignment (drawingRoutePlanarCoreFormula graph) ∧
        ∀ node,
          assignment (.inl node) = routeAssignment node.routeKey := by
  let carrierAssignment : CarrierNode → Bool :=
    routeAssignment ∘ CarrierNode.routeKey
  have boundaryLaws :
      ∀ crossing ∈ orientedCrossingHalo graph,
        carrierAssignment
            (carrierNodeCrossingPorts crossing).aLeft =
            carrierAssignment
              (carrierNodeCrossingPorts crossing).aRight ∧
          carrierAssignment
              (carrierNodeCrossingPorts crossing).bTop =
            carrierAssignment
              (carrierNodeCrossingPorts crossing).bBottom := by
    intro crossing crossingMem
    exact ⟨rfl, rfl⟩
  have crossoverExtension :
      CrossoverFamilyExtends carrierAssignment
        (orientedCrossingHalo graph)
        carrierNodeCrossingPorts crossingMacroOrigin 1 :=
    (crossoverFamilyExtends_iff carrierAssignment
      (orientedCrossingHalo graph)
      carrierNodeCrossingPorts crossingMacroOrigin 1).mpr
        boundaryLaws
  rcases crossoverExtension with ⟨internal, crossoverHolds⟩
  let assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool :=
    Sum.elim carrierAssignment internal
  refine ⟨assignment,
    (drawingRoutePlanarCoreFormula_holds_iff graph assignment).mpr
      ⟨crossoverHolds, ?_⟩, ?_⟩
  · have routeHolds :=
      drawingRouteWireFormula_holds graph routeAssignment
    have restriction :
        assignment ∘ Sum.inl =
          routeAssignment ∘ CarrierNode.routeKey := by
      funext node
      rfl
    rw [restriction]
    exact routeHolds
  · intro node
    rfl

/-- Every satisfying complete core assignment obeys all crossover,
straight-carrier, and route-bend propagation laws. -/
theorem drawingRoutePlanarCoreFormula_boundary_laws
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool)
    (holds : FormulaHolds assignment
      (drawingRoutePlanarCoreFormula graph)) :
    (∀ crossing ∈ orientedCrossingHalo graph,
      assignment
          (.inl (.boundary ⟨crossing, .left⟩)) =
          assignment
            (.inl (.boundary ⟨crossing, .right⟩)) ∧
        assignment
            (.inl (.boundary ⟨crossing, .top⟩)) =
          assignment
            (.inl (.boundary ⟨crossing, .bottom⟩))) ∧
      (∀ link ∈ drawingCompleteCarrierLinks graph,
        assignment (.inl link.first) =
          assignment (.inl link.second)) ∧
      ∀ link ∈ drawingRouteBendLinks graph,
        assignment (.inl link.first) =
          assignment (.inl link.second) := by
  have components :=
    (drawingRoutePlanarCoreFormula_holds_iff graph assignment).mp holds
  constructor
  · simpa [carrierNodeCrossingPorts] using
      crossoverFamily_boundary_eq assignment
        (orientedCrossingHalo graph)
        carrierNodeCrossingPorts crossingMacroOrigin 1
        components.1
  · have wireComponents :
        FormulaHolds (assignment ∘ Sum.inl)
            (drawingCompleteCarrierFormula graph) ∧
          FormulaHolds (assignment ∘ Sum.inl)
            (drawingRouteBendFormula graph) :=
      (formulaHolds_route_append_iff
        (assignment ∘ Sum.inl)
        (drawingCompleteCarrierFormula graph)
        (drawingRouteBendFormula graph)).mp components.2
    constructor
    · exact (equalityFamily_holds_iff
        (assignment ∘ Sum.inl)
        (drawingCompleteCarrierLinks graph)).mp wireComponents.1
    · exact (equalityFamily_holds_iff
        (assignment ∘ Sum.inl)
        (drawingRouteBendLinks graph)).mp wireComponents.2

end PeriodicOrthocrossing
end LeanTrominoes
