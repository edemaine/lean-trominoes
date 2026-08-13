/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarThreeSATThree
import LeanTrominoes.PeriodicOneInThreeCorrectness
import LeanTrominoes.PeriodicOneInThreeOccurrences

/-!
# Periodic planar 1-in-3SAT-3 semantics

This file applies the exact-one clause gadget only after the routed planar
formula's variable occurrences have been split.  This order is essential:
the planar crossover gadgets can have high-degree internal variables, while
the implication-cycle construction restores the three-occurrence bound.

The result is the logical periodic 1-in-3SAT-3 instance underlying the
positioned Figure 9 drawing.  Its geometric realization is kept separate so
that the semantic and occurrence arguments do not depend on coordinate
bookkeeping.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Clause-scoped variables of the direct Figure 9 image. -/
abbrev PeriodicPlanarOneInThreeThreeRawVariable (Variable : Type*) :=
  OneInThreeVariable
    (PeriodicPlanarThreeSATThreeVariable Variable)

/-- Keep the equality test for a split routed clause opaque.  This avoids
exceeding the typeclass search depth when the clause is nested inside the
identity of a Figure 9 auxiliary variable. -/
opaque periodicPlanarThreeSATThreeClauseDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (PeriodicClause
        (PeriodicPlanarThreeSATThreeVariable Variable)) := by
  infer_instance

instance periodicPlanarThreeSATThreeClauseInstDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (PeriodicClause
        (PeriodicPlanarThreeSATThreeVariable Variable)) :=
  periodicPlanarThreeSATThreeClauseDecidableEq

/-- Keep the constructive equality procedure for the clause-scoped Figure 9
type opaque to the elaborator.  Its compiled body is the ordinary derived
equality test. -/
opaque periodicPlanarOneInThreeThreeRawVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) := by
  infer_instance

instance periodicPlanarOneInThreeThreeRawVariableInstDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  periodicPlanarOneInThreeThreeRawVariableDecidableEq

/-- The direct Figure 9 image before putting its large clause-scoped variable
type behind the generic opaque wrapper. -/
def drawingPeriodicPlanarOneInThreeThreeRawFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThree.formula
    (drawingPeriodicPlanarThreeSATThreeFormula formula)

/-- The exact-one image of the occurrence-split routed planar SAT formula.
The final opaque wrapper changes neither literals nor semantics; it keeps the
equality test stored by occurrence-bound propositions compact. -/
def drawingPeriodicPlanarOneInThreeThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  wrapPeriodicPlanarSATFormula
    (drawingPeriodicPlanarOneInThreeThreeRawFormula formula)

/-- Exact-one truth of a clause is unchanged by the opaque wrapper. -/
theorem wrapPeriodicPlanarSATClause_oneInThree_holds
    {Original : Type*}
    (assignment : Original → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Original) :
    PeriodicOneInThree.ClauseHolds assignment translate clause ↔
      PeriodicOneInThree.ClauseHolds
        (wrapPeriodicPlanarSATAssignment assignment)
        translate (wrapPeriodicPlanarSATClause clause) := by
  simp [PeriodicOneInThree.ClauseHolds,
    PeriodicOneInThree.clauseValues,
    wrapPeriodicPlanarSATClause,
    wrapPeriodicPlanarSATLiteral,
    wrapPeriodicPlanarSATAssignment,
    List.map_map, Function.comp_def]

/-- The converse assignment map preserves the same exact-one clause values. -/
theorem unwrap_wrapPeriodicPlanarSATClause_oneInThree_holds
    {Original : Type*}
    (assignment : WrappedPeriodicVariable Original → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Original) :
    PeriodicOneInThree.ClauseHolds assignment translate
        (wrapPeriodicPlanarSATClause clause) ↔
      PeriodicOneInThree.ClauseHolds
        (unwrapPeriodicPlanarSATAssignment assignment)
        translate clause := by
  simp [PeriodicOneInThree.ClauseHolds,
    PeriodicOneInThree.clauseValues,
    wrapPeriodicPlanarSATClause,
    wrapPeriodicPlanarSATLiteral,
    unwrapPeriodicPlanarSATAssignment,
    List.map_map, Function.comp_def]

/-- Opaque variable wrapping preserves periodic exact-one satisfiability. -/
theorem wrapPeriodicPlanarSATFormula_oneInThree_satisfiable_iff
    {Original : Type*} (source : PeriodicCNF Original) :
    PeriodicOneInThree.Satisfiable
        (wrapPeriodicPlanarSATFormula source) ↔
      PeriodicOneInThree.Satisfiable source := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    refine ⟨unwrapPeriodicPlanarSATAssignment assignment, ?_⟩
    intro translate clause clauseMem
    apply
      (unwrap_wrapPeriodicPlanarSATClause_oneInThree_holds
        assignment translate clause).mp
    apply satisfies translate (wrapPeriodicPlanarSATClause clause)
    exact List.mem_map.mpr ⟨clause, clauseMem, rfl⟩
  · rintro ⟨assignment, satisfies⟩
    refine ⟨wrapPeriodicPlanarSATAssignment assignment, ?_⟩
    intro translate wrappedClause wrappedClauseMem
    rcases List.mem_map.mp wrappedClauseMem with
      ⟨clause, clauseMem, wrappedClauseEq⟩
    subst wrappedClause
    apply
      (wrapPeriodicPlanarSATClause_oneInThree_holds
        assignment translate clause).mp
    exact satisfies translate clause clauseMem

/-- Every generated exact-one clause has width at most three. -/
theorem drawingPeriodicPlanarOneInThreeThreeFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPeriodicPlanarOneInThreeThreeFormula formula).WidthAtMost 3 := by
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact PeriodicOneInThree.formula_widthAtMostThree
    (drawingPeriodicPlanarThreeSATThreeFormula formula)

/-- Figure 9 preserves the three-occurrence bound established by the
post-planarization cycle split. -/
theorem drawingPeriodicPlanarOneInThreeThreeFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    (drawingPeriodicPlanarOneInThreeThreeFormula formula).OccurrencesAtMost
      3 := by
  apply wrapPeriodicPlanarSATFormula_occurrencesAtMost
  let sourceDecEq :
      DecidableEq
        (PeriodicPlanarThreeSATThreeVariable Variable) :=
    inferInstance
  have defaultSourceOccurrences :=
    drawingPeriodicPlanarThreeSATThreeFormula_occurrencesAtMostThree
      formula
  have sourceOccurrences :
      @PeriodicCNF.OccurrencesAtMost
        (PeriodicPlanarThreeSATThreeVariable Variable)
        (@instBEqOfDecidableEq
          (PeriodicPlanarThreeSATThreeVariable Variable)
          sourceDecEq)
        (by infer_instance) 3
        (drawingPeriodicPlanarThreeSATThreeFormula formula) := by
    apply PeriodicCNF.occurrencesAtMost_congr_beq
    exact defaultSourceOccurrences
  have generatedOccurrences :=
    @PeriodicOneInThree.formula_occurrencesAtMostThree
      (PeriodicPlanarThreeSATThreeVariable Variable)
      sourceDecEq
      (drawingPeriodicPlanarThreeSATThreeFormula formula)
      (drawingPeriodicPlanarThreeSATThreeFormula_widthAtMostThree
        formula sourceWidth)
      sourceOccurrences
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (drawingPeriodicPlanarOneInThreeThreeRawFormula formula)
    generatedOccurrences

/-- The exact-one gadget preserves satisfiability relative to the
occurrence-split routed formula. -/
theorem
    drawingPeriodicPlanarOneInThreeThreeFormula_satisfiable_iff_threeSATThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingPeriodicPlanarOneInThreeThreeFormula formula) ↔
      (drawingPeriodicPlanarThreeSATThreeFormula formula).Satisfiable := by
  exact
    (wrapPeriodicPlanarSATFormula_oneInThree_satisfiable_iff
      (drawingPeriodicPlanarOneInThreeThreeRawFormula formula)).trans
        (PeriodicOneInThree.satisfiable_iff
          (drawingPeriodicPlanarThreeSATThreeFormula formula)
          (drawingPeriodicPlanarThreeSATThreeFormula_widthAtMostThree
            formula sourceWidth)).symm

/-- End-to-end correctness of planarization, occurrence splitting, and the
exact-one replacement. -/
theorem drawingPeriodicPlanarOneInThreeThreeFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingPeriodicPlanarOneInThreeThreeFormula formula) ↔
      formula.Satisfiable := by
  rw [
    drawingPeriodicPlanarOneInThreeThreeFormula_satisfiable_iff_threeSATThree
      formula sourceWidth,
    drawingPeriodicPlanarThreeSATThreeFormula_satisfiable_iff
      formula sourceOccurrences]

end PeriodicOrthocrossing
end LeanTrominoes
