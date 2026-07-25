import LeanTrominoes.PeriodicOrthocrossingPlanarWires

/-!
# The crossover-and-wire planarization core

The crossover formulas already use a sum of boundary and site-scoped internal
variables.  We rename the equality-wire formulas into the boundary summand and
append the two clause families.  The resulting finite embedded formula has an
exact semantic interface to assignments on translated segment occurrences.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

private theorem formulaHolds_append_iff
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

/-- Rename every wire-boundary variable into the external summand used by
the crossover family. -/
def scopedDrawingWireFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause
      (Sum CrossingBoundary (CrossingRecord × CrossoverInternal))) :=
  (drawingWireFormula graph).map fun clause =>
    clause.rename fun boundary =>
      (Sum.inl boundary :
        Sum CrossingBoundary (CrossingRecord × CrossoverInternal))

@[simp]
theorem scopedDrawingWireFormula_holds_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CrossingBoundary (CrossingRecord × CrossoverInternal) → Bool) :
    FormulaHolds assignment (scopedDrawingWireFormula graph) ↔
      FormulaHolds (assignment ∘ Sum.inl)
        (drawingWireFormula graph) := by
  exact formulaHolds_map assignment
    (fun boundary =>
      (Sum.inl boundary :
        Sum CrossingBoundary (CrossingRecord × CrossoverInternal)))
    id (drawingWireFormula graph)

/-- The finite embedded formula consisting of every crossover macrocell and
every equality link between consecutive crossing sites. -/
def drawingPlanarCoreFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause
      (Sum CrossingBoundary (CrossingRecord × CrossoverInternal))) :=
  drawingCrossoverFormula graph ++ scopedDrawingWireFormula graph

/-- Satisfaction of the planar core splits into its crossover and wire
components. -/
theorem drawingPlanarCoreFormula_holds_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CrossingBoundary (CrossingRecord × CrossoverInternal) → Bool) :
    FormulaHolds assignment (drawingPlanarCoreFormula graph) ↔
      FormulaHolds assignment (drawingCrossoverFormula graph) ∧
        FormulaHolds (assignment ∘ Sum.inl)
          (drawingWireFormula graph) := by
  rw [drawingPlanarCoreFormula,
    formulaHolds_append_iff,
    scopedDrawingWireFormula_holds_iff]

/-- Every assignment on translated segment-occurrence carriers extends to a
satisfying assignment of the complete crossover-and-wire core, while
retaining the requested value on every external boundary variable. -/
theorem exists_drawingPlanarCoreFormula_holds_of_carrierAssignment
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (carrierAssignment : (Nat × Nat × Cell) → Bool) :
    ∃ assignment :
        Sum CrossingBoundary (CrossingRecord × CrossoverInternal) → Bool,
      FormulaHolds assignment (drawingPlanarCoreFormula graph) ∧
        ∀ boundary,
          assignment (.inl boundary) =
            carrierAssignment boundary.carrierKey := by
  let boundaryAssignment :=
    carrierBoundaryAssignment carrierAssignment
  rcases drawingCrossoversExtend_carrierBoundaryAssignment
      graph carrierAssignment with
    ⟨internal, crossoverHolds⟩
  let assignment :
      Sum CrossingBoundary (CrossingRecord × CrossoverInternal) → Bool :=
    Sum.elim boundaryAssignment internal
  refine ⟨assignment,
    (drawingPlanarCoreFormula_holds_iff graph assignment).mpr
      ⟨crossoverHolds, ?_⟩, ?_⟩
  · have wireHolds :=
      drawingWireFormula_holds_carrierBoundaryAssignment
        graph carrierAssignment
    have restriction :
        assignment ∘ Sum.inl = boundaryAssignment := by
      funext boundary
      rfl
    rw [restriction]
    exact wireHolds
  · intro boundary
    rfl

/-- Every satisfying core assignment obeys both the opposite-port laws
inside crossovers and the equality laws on all links between sites. -/
theorem drawingPlanarCoreFormula_boundary_laws
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CrossingBoundary (CrossingRecord × CrossoverInternal) → Bool)
    (holds : FormulaHolds assignment
      (drawingPlanarCoreFormula graph)) :
    (∀ crossing ∈ orientedCrossings graph,
      assignment (.inl ⟨crossing, .left⟩) =
          assignment (.inl ⟨crossing, .right⟩) ∧
        assignment (.inl ⟨crossing, .top⟩) =
          assignment (.inl ⟨crossing, .bottom⟩)) ∧
      ∀ link ∈ drawingWireLinks graph,
        assignment (.inl link.first) =
          assignment (.inl link.second) := by
  have components :=
    (drawingPlanarCoreFormula_holds_iff graph assignment).mp holds
  constructor
  · exact drawingCrossoverFormula_boundary_eq
      graph assignment components.1
  · exact (equalityFamily_holds_iff
      (assignment ∘ Sum.inl) (drawingWireLinks graph)).mp
        components.2

end PeriodicOrthocrossing
end LeanTrominoes
