/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationSourceIndexedClausePositions

/-! # A common row index for formula and geometric incidence columns -/
namespace LeanTrominoes.PositionedIncidenceRows
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
abbrev Row (Variable : Type*) :=
  (PositionedPeriodicClause Variable × Nat) × (PeriodicLiteral Variable × Nat)

def rows {Variable : Type*} (source : PositionedPeriodicCNF Variable) : List (Row Variable) :=
  source.clauses.zipIdx.flatMap fun clause => clause.1.literals.zipIdx.map fun literal => (clause, literal)

theorem mem_rows {Variable : Type*} (source : PositionedPeriodicCNF Variable) (row : Row Variable) :
    row ∈ rows source ↔ row.1 ∈ source.clauses.zipIdx ∧ row.2 ∈ row.1.1.literals.zipIdx := by
  simp [rows, List.mem_flatMap, List.mem_map, Prod.ext_iff]

private theorem flatMap_ignore_index {A B : Type*} (values : List A) (f : A → List B) :
    values.zipIdx.flatMap (fun p => f p.1) = values.flatMap f := by
  rw [← List.flatMap_map, List.zipIdx_map_fst]

private theorem map_ignore_index {A B : Type*} (values : List A) (f : A → B) :
    values.zipIdx.map (fun p => f p.1) = values.map f := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map f) (List.zipIdx_map_fst 0 values)

theorem atoms {Variable : Type*} (source : PositionedPeriodicCNF Variable) :
    (rows source).map (fun row => row.2.1.atom) = source.erase.variableOccurrences := by
  simp only [rows, List.map_flatMap, List.map_map, Function.comp_def]
  simp_rw [map_ignore_index]
  rw [flatMap_ignore_index source.clauses (fun c => c.literals.map PeriodicLiteral.atom)]
  simp [PeriodicCNF.variableOccurrences, PositionedPeriodicCNF.erase, List.flatMap_map]

theorem clausePositions {Variable : Type*} (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    (rows source).map (fun row => PositionedPeriodicCNF.canonicalClausePosition placement row.1.1) =
      presentedIncidenceClausePositions source placement := by
  simp only [rows, List.map_flatMap, List.map_map, Function.comp_def]
  simp only [List.map_const', List.length_zipIdx]
  rw [flatMap_ignore_index source.clauses (fun c => List.replicate c.literals.length
    (PositionedPeriodicCNF.canonicalClausePosition placement c))]
  rfl

theorem directionWords {Variable : Type*} (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (rows source).map (fun row => Gadget.unitSubdivisionDirections (routes row.1.2 row.2.2)) =
      presentedIncidenceDirectionWords source routes := by
  simp only [rows, List.map_flatMap, List.map_map, Function.comp_def,
    presentedIncidenceDirectionWords]

/-- Recovered anchored offsets are exactly the offsets of the normalized formula. -/
theorem anchoredOffsets {Variable Output : Type*} (source : PositionedPeriodicCNF Variable)
    (value : Cell → Output) :
    (rows source).map (fun row => value
      (Cell.sub row.2.1.offset (PeriodicCNF.clauseAnchor row.1.1.literals))) =
      source.erase.anchorNormalize.clauses.flatMap (fun clause => clause.map (fun literal => value literal.offset)) := by
  simp only [rows, List.map_flatMap, List.map_map, Function.comp_def]
  have drop (c : PositionedPeriodicClause Variable) :
      c.literals.zipIdx.map (fun l => value (Cell.sub l.1.offset (PeriodicCNF.clauseAnchor c.literals))) =
      c.literals.map (fun l => value (Cell.sub l.offset (PeriodicCNF.clauseAnchor c.literals))) :=
    map_ignore_index c.literals (fun l => value (Cell.sub l.offset (PeriodicCNF.clauseAnchor c.literals)))
  simp_rw [drop]
  rw [flatMap_ignore_index source.clauses (fun c => c.literals.map
    (fun l => value (Cell.sub l.offset (PeriodicCNF.clauseAnchor c.literals))))]
  simp [PeriodicCNF.anchorNormalize, PeriodicClause.anchorNormalize,
    PeriodicLiteral.anchorNormalize, PositionedPeriodicCNF.erase, List.flatMap_map, List.map_map, Function.comp_def]

end LeanTrominoes.PositionedIncidenceRows
