/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarBoundedLocalCompleteness
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFinalGauge

/-! # One-dimensional planar SAT endpoints

Both supplied-drawing reductions preserve one-dimensionality, locality,
three occurrences, and the intrinsic linear grid bound.
-/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT
open PeriodicOrthocrossing
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
variable {V : Type} [Primcodable V] [DecidableEq V]

namespace Orbit

def LocalOneDimensionalProblem (i : Input V) : Prop :=
  i.1.IsOneDimensional ∧ BoundedLocalProblem i

def LocalOneDimensionalThreeOccurrenceProblem (i : Input V) : Prop :=
  i.1.IsOneDimensional ∧ BoundedLocalThreeOccurrenceProblem i
end Orbit

namespace Unbounded

def LocalOneDimensionalExactOneProblem (i : Input V) : Prop :=
  i.1.IsOneDimensional ∧ BoundedLocalExactOneProblem i

def LocalOneDimensionalExactOneThreeOccurrenceProblem (i : Input V) : Prop :=
  i.1.IsOneDimensional ∧ BoundedLocalExactOneThreeOccurrenceProblem i
end Unbounded

namespace ThreeOccurrenceGeometry

omit [Primcodable V] in
theorem isOneDimensional (f : PeriodicCNF V) (hl : f.IsLocal)
    (hw : f.WidthAtMost 3) (ho : f.OccurrencesAtMost 3) (hd : f.IsOneDimensional) :
    (input f).1.IsOneDimensional := by
  apply retainedFigureNineClearancePositionedFormula_erase_isOneDimensional
  · exact PeriodicCNF.incidenceGraph_isWellFormed f
  · exact PeriodicCNF.incidenceGraph_degreeAtMost hw ho
  · exact PeriodicCNF.incidenceGraph_isLocal hl
  · exact PeriodicCNF.incidenceGraph_hasZeroVerticalOffsets hd

theorem localOneDimensionalThreeOccurrence_correct (f : PeriodicCNF V)
    (hl : f.IsLocal) (hw : f.WidthAtMost 3) (ho : f.OccurrencesAtMost 3)
    (hn : ∀ c ∈ f.clauses, c ≠ []) (hd : f.IsOneDimensional) :
    Orbit.LocalOneDimensionalThreeOccurrenceProblem (input f) ↔ f.Satisfiable := by
  have horizontal := isOneDimensional f hl hw ho hd
  have locality : (input f).1.IsLocal := isLocal f hl hw ho
  have grid : GridBound 8847360 (input f) := drawing_gridSize_le_output_size f ho hn
  simp only [Orbit.LocalOneDimensionalThreeOccurrenceProblem,
    Orbit.BoundedLocalThreeOccurrenceProblem,Orbit.LocalThreeOccurrenceProblem,
    horizontal,grid,locality,true_and]
  exact input_correct f hl hw ho hn

theorem localOneDimensional_correct (f : PeriodicCNF V)
    (hl : f.IsLocal) (hw : f.WidthAtMost 3) (ho : f.OccurrencesAtMost 3)
    (hn : ∀ c ∈ f.clauses, c ≠ []) (hd : f.IsOneDimensional) :
    Orbit.LocalOneDimensionalProblem (input f) ↔ f.Satisfiable := by
  have full := localOneDimensionalThreeOccurrence_correct f hl hw ho hn hd
  constructor
  · intro h
    exact (input_correct f hl hw ho hn).1
      ⟨PeriodicCNF.occurrencesAtMost_congr_beq _ _ _ _ 3 _
        (retainedFigureNineClearancePositionedFormula_occurrencesAtMostThree f hl hw ho hn),h.2.2.2⟩
  · intro h
    obtain ⟨horizontal,grid,locality,_,problem⟩ := full.2 h
    exact ⟨horizontal,grid,locality,problem⟩
end ThreeOccurrenceGeometry

namespace ExactOneEndpoint
local instance oneDimensionalTargetDecidableEq : DecidableEq (Target V) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

omit [Primcodable V] in
theorem isOneDimensional (f : PeriodicCNF V) (hl : f.IsLocal)
    (hw : f.WidthAtMost 3) (ho : f.OccurrencesAtMost 3)
    (hn : ∀ c ∈ f.clauses, c ≠ []) (hd : f.IsOneDimensional) :
    (input f).1.IsOneDimensional := by
  change (positioned f).erase.IsOneDimensional
  rw [positioned,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn]
  exact retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_erase_isOneDimensional
    (PeriodicCNF.incidenceGraph_isWellFormed f)
    (PeriodicCNF.incidenceGraph_degreeAtMost hw ho)
    (PeriodicCNF.incidenceGraph_isLocal hl) hl hw ho hn
    (PeriodicCNF.incidenceGraph_hasZeroVerticalOffsets hd)

theorem localOneDimensional_correct (f : PeriodicCNF V)
    (hl : f.IsLocal) (hw : f.WidthAtMost 3) (ho : f.OccurrencesAtMost 3)
    (hn : ∀ c ∈ f.clauses, c ≠ []) (hd : f.IsOneDimensional) :
    Unbounded.LocalOneDimensionalExactOneProblem (input f) ↔ f.Satisfiable := by
  have horizontal := isOneDimensional f hl hw ho hn hd
  have locality := isLocal f hl hw ho hn
  have grid : GridBound 637009920 (input f) := drawing_gridSize_le_output_size f hl hw ho hn
  simp only [Unbounded.LocalOneDimensionalExactOneProblem,
    Unbounded.BoundedLocalExactOneProblem,Unbounded.LocalExactOneProblem,
    horizontal,grid,locality,true_and]
  exact problem_correct f hl hw ho hn

theorem localOneDimensionalThreeOccurrence_correct (f : PeriodicCNF V)
    (hl : f.IsLocal) (hw : f.WidthAtMost 3) (ho : f.OccurrencesAtMost 3)
    (hn : ∀ c ∈ f.clauses, c ≠ []) (hd : f.IsOneDimensional) :
    Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem (input f) ↔ f.Satisfiable := by
  have base := localOneDimensional_correct f hl hw ho hn hd
  constructor
  · rintro ⟨horizontal,grid,locality,_,problem⟩
    exact base.1 ⟨horizontal,grid,locality,problem⟩
  · intro h
    obtain ⟨horizontal,grid,locality,problem⟩ := base.2 h
    exact ⟨horizontal,grid,locality,
      PeriodicCNF.occurrencesAtMost_congr_beq _ _ _ _ 3 _ (occurrences f hl hw ho hn),problem⟩
end ExactOneEndpoint
end LeanTrominoes.PeriodicPlanarSAT
