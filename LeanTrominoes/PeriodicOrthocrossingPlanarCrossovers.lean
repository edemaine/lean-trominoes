/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingNormalization
import LeanTrominoes.PlanarThreeSATFamilyExtensions

/-!
# Crossover gadgets at canonical drawing crossings

The horizontal-first crossing records now serve as concrete gadget-site keys.
Each site receives four distinct boundary-wire variables and a positioned
Figure 8 crossover in a `20 × 20` macrocell.  The internal variables remain
scoped by the complete crossing record.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The four boundary directions of an oriented crossover site. -/
inductive CrossingSide
  | left
  | right
  | top
  | bottom
  deriving DecidableEq, Repr

/-- One external boundary variable of one canonical crossing site. -/
structure CrossingBoundary where
  crossing : CrossingRecord
  side : CrossingSide
  deriving DecidableEq, Repr

/-- Normalize a physical crossover boundary to its canonical crossing site,
preserving which of the four ports it names. -/
def CrossingBoundary.periodNormalize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) : CrossingBoundary :=
  ⟨boundary.crossing.periodNormalize graph, boundary.side⟩

/-- The paper uses a common factor 20 to accommodate both Figure 8
macrocells. -/
def planarMacroScale : Int := 20

/-- The lower-left origin of the macrocell replacing a drawing-grid point. -/
def crossingMacroOrigin (crossing : CrossingRecord) : Cell :=
  Cell.scale planarMacroScale crossing.point

/-- Four distinct external variables attached to one canonical crossing. -/
def crossingPorts (crossing : CrossingRecord) :
    CrossoverPorts CrossingBoundary where
  aLeft := ⟨crossing, .left⟩
  aRight := ⟨crossing, .right⟩
  bTop := ⟨crossing, .top⟩
  bBottom := ⟨crossing, .bottom⟩

/-- All positioned crossover clauses in one drawing fundamental square. -/
def drawingCrossoverFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause
      (Sum CrossingBoundary (CrossingRecord × CrossoverInternal))) :=
  crossoverFamily (orientedCrossingHalo graph)
    crossingPorts crossingMacroOrigin 1

/-- An assignment to the four external variables of every crossing extends
to all fresh crossover internals. -/
def DrawingCrossoversExtend
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : CrossingBoundary → Bool) : Prop :=
  CrossoverFamilyExtends assignment (orientedCrossingHalo graph)
    crossingPorts crossingMacroOrigin 1

/-- The drawing's complete crossover family extends exactly when each
horizontal and vertical pair of boundary variables agrees. -/
theorem drawingCrossoversExtend_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : CrossingBoundary → Bool) :
    DrawingCrossoversExtend graph assignment ↔
      ∀ crossing ∈ orientedCrossingHalo graph,
        assignment ⟨crossing, .left⟩ =
            assignment ⟨crossing, .right⟩ ∧
          assignment ⟨crossing, .top⟩ =
            assignment ⟨crossing, .bottom⟩ := by
  exact crossoverFamilyExtends_iff assignment
    (orientedCrossingHalo graph)
    crossingPorts crossingMacroOrigin 1

/-- The occurrence key of the carrier passing through a crossing boundary.
Left and right use the horizontal occurrence; top and bottom use the vertical
occurrence. -/
def CrossingBoundary.carrierKey (boundary : CrossingBoundary) :
    Nat × Nat × Cell :=
  match boundary.side with
  | .left | .right =>
      PeriodicGridDrawing.SegmentOccurrenceKey
        boundary.crossing.first boundary.crossing.firstTranslate
  | .top | .bottom =>
      PeriodicGridDrawing.SegmentOccurrenceKey
        boundary.crossing.second boundary.crossing.secondTranslate

/-- Pull an assignment on segment occurrences back to all crossing
boundaries. -/
def carrierBoundaryAssignment
    (assignment : (Nat × Nat × Cell) → Bool) :
    CrossingBoundary → Bool :=
  fun boundary => assignment boundary.carrierKey

/-- Every assignment that is constant on each segment occurrence extends
through all canonical crossover gadgets simultaneously. -/
theorem drawingCrossoversExtend_carrierBoundaryAssignment
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : (Nat × Nat × Cell) → Bool) :
    DrawingCrossoversExtend graph
      (carrierBoundaryAssignment assignment) := by
  apply (drawingCrossoversExtend_iff graph _).mpr
  intro crossing crossingMem
  exact ⟨rfl, rfl⟩

/-- Conversely, every satisfying complete crossover assignment propagates
both carrier signals at every canonical drawing crossing. -/
theorem drawingCrossoverFormula_boundary_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CrossingBoundary (CrossingRecord × CrossoverInternal) → Bool)
    (holds : FormulaHolds assignment (drawingCrossoverFormula graph)) :
    ∀ crossing ∈ orientedCrossingHalo graph,
      assignment (.inl ⟨crossing, .left⟩) =
          assignment (.inl ⟨crossing, .right⟩) ∧
        assignment (.inl ⟨crossing, .top⟩) =
          assignment (.inl ⟨crossing, .bottom⟩) := by
  exact crossoverFamily_boundary_eq assignment
    (orientedCrossingHalo graph)
    crossingPorts crossingMacroOrigin 1 holds

end PeriodicOrthocrossing
end LeanTrominoes
