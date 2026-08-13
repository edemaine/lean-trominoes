/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOneInThree
import LeanTrominoes.PeriodicCNFPlanarPeriodicSoundness

/-!
# Correctness of the periodic positioned exact-one reduction

At each translated routed block, the verified Figure 9 extension chooses the
clause-local auxiliary values.  Because those auxiliaries are proto-variables
at offset zero, the choices assemble into one plane-wide periodic assignment.
Conversely, restricting any exact-one assignment to its original-variable
summand recovers a routed planar SAT assignment block by block.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Extend a periodic routed SAT assignment with Figure 9 auxiliaries,
choosing the auxiliary values independently in each translated block. -/
def extendPeriodicPlanarOneInThreeAssignment
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool) :
    PeriodicPlanarOneInThreeVariable Variable →
      Cell → Bool
  | .inl original, cell =>
      assignment original cell
  | .inr auxiliary, cell =>
      PlanarOneInThree.extendAssignment
        (planarSATFiniteAssignmentAt formula assignment cell)
        (.inr auxiliary)

/-- The finite assignment induced from the plane-wide extension is exactly
the finite Figure 9 extension of the corresponding routed block. -/
theorem planarOneInThreeFiniteAssignmentAt_extend
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (translate : Cell) :
    planarOneInThreeFiniteAssignmentAt
        formula
        (extendPeriodicPlanarOneInThreeAssignment formula assignment)
        translate =
      PlanarOneInThree.extendAssignment
        (planarSATFiniteAssignmentAt formula assignment translate) := by
  funext inputVariable
  cases inputVariable with
  | inl original =>
      cases original with
      | inl node =>
          cases node with
          | carrier carrierNode =>
              cases carrierNode with
              | terminal terminal =>
                  simp [planarOneInThreeFiniteAssignmentAt,
                    normalizePlanarOneInThreeVariable,
                    normalizePlanarSATVariable,
                    extendPeriodicPlanarOneInThreeAssignment,
                    PlanarOneInThree.extendAssignment,
                    PlanarOneInThree.constantAssignment,
                    planarSATFiniteAssignmentAt]
              | boundary boundary =>
                  simp [planarOneInThreeFiniteAssignmentAt,
                    normalizePlanarOneInThreeVariable,
                    normalizePlanarSATVariable,
                    extendPeriodicPlanarOneInThreeAssignment,
                    PlanarOneInThree.extendAssignment,
                    PlanarOneInThree.constantAssignment,
                    planarSATFiniteAssignmentAt,
                    Cell.add]
          | atom site =>
              rcases site with ⟨atom, cell⟩
              simp [planarOneInThreeFiniteAssignmentAt,
                normalizePlanarOneInThreeVariable,
                normalizePlanarSATVariable,
                extendPeriodicPlanarOneInThreeAssignment,
                PlanarOneInThree.extendAssignment,
                PlanarOneInThree.constantAssignment,
                planarSATFiniteAssignmentAt]
      | inr internal =>
          simp [planarOneInThreeFiniteAssignmentAt,
            normalizePlanarOneInThreeVariable,
            normalizePlanarSATVariable,
            extendPeriodicPlanarOneInThreeAssignment,
            PlanarOneInThree.extendAssignment,
            PlanarOneInThree.constantAssignment,
            planarSATFiniteAssignmentAt, Cell.add]
  | inr auxiliary =>
      simp [planarOneInThreeFiniteAssignmentAt,
        normalizePlanarOneInThreeVariable,
        extendPeriodicPlanarOneInThreeAssignment,
        Cell.add]

/-- A satisfying routed planar SAT assignment extends to a satisfying
periodic positioned exact-one assignment. -/
theorem drawingPeriodicPlanarOneInThreeFormula_satisfies_of_planarSAT
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (planarHolds :
      (drawingPeriodicPlanarSATFormula formula).Satisfies
        assignment) :
    PeriodicOneInThree.Satisfies
      (drawingPeriodicPlanarOneInThreeFormula formula)
      (extendPeriodicPlanarOneInThreeAssignment
        formula assignment) := by
  apply
    (drawingPeriodicPlanarOneInThreeFormula_satisfies_iff
      formula
      (extendPeriodicPlanarOneInThreeAssignment
        formula assignment)).mpr
  have finitePlanarHolds :=
    (drawingPeriodicPlanarSATFormula_satisfies_iff
      formula assignment).mp planarHolds
  have finiteWidth :
      ∀ clause ∈ drawingPlanarSATFormula formula,
        clause.literals.length ≤ 3 := by
    simpa [FormulaWidthAtMost,
      EmbeddedClause.WidthAtMost] using
      drawingPlanarSATFormula_widthAtMostThree
        formula sourceWidth
  intro translate
  rw [planarOneInThreeFiniteAssignmentAt_extend formula]
  exact PlanarOneInThree.formula_complete
    (drawingPlanarSATFormula formula)
    finiteWidth
    (planarSATFiniteAssignmentAt formula assignment translate)
    (finitePlanarHolds translate)

/-- Restrict a periodic positioned exact-one assignment to its normalized
original routed variables. -/
def restrictPeriodicPlanarOneInThreeAssignment
    {Variable : Type*}
    (assignment :
      PeriodicPlanarOneInThreeVariable Variable →
        Cell → Bool) :
    PeriodicPlanarSATVariable Variable → Cell → Bool :=
  fun original cell => assignment (.inl original) cell

/-- Finite restriction commutes with the two periodicization maps. -/
theorem planarSATFiniteAssignmentAt_restrict
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarOneInThreeVariable Variable →
        Cell → Bool)
    (translate : Cell) :
    planarSATFiniteAssignmentAt
        formula
        (restrictPeriodicPlanarOneInThreeAssignment assignment)
        translate =
      PlanarOneInThree.restrictAssignment
        (planarOneInThreeFiniteAssignmentAt
          formula assignment translate) := by
  funext original
  cases original with
  | inl node =>
      cases node with
      | carrier carrierNode =>
          cases carrierNode with
          | terminal terminal =>
              rfl
          | boundary boundary =>
              rfl
      | atom site =>
          rfl
  | inr internal =>
      rfl

/-- Any satisfying periodic positioned exact-one assignment restricts to a
satisfying periodic routed planar SAT assignment. -/
theorem drawingPeriodicPlanarSATFormula_satisfies_of_oneInThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3)
    (assignment :
      PeriodicPlanarOneInThreeVariable Variable →
        Cell → Bool)
    (oneInThreeHolds :
      PeriodicOneInThree.Satisfies
        (drawingPeriodicPlanarOneInThreeFormula formula)
        assignment) :
    (drawingPeriodicPlanarSATFormula formula).Satisfies
      (restrictPeriodicPlanarOneInThreeAssignment
        assignment) := by
  apply
    (drawingPeriodicPlanarSATFormula_satisfies_iff
      formula
      (restrictPeriodicPlanarOneInThreeAssignment
        assignment)).mpr
  have finiteOneInThreeHolds :=
    (drawingPeriodicPlanarOneInThreeFormula_satisfies_iff
      formula assignment).mp oneInThreeHolds
  have finiteWidth :
      ∀ clause ∈ drawingPlanarSATFormula formula,
        clause.literals.length ≤ 3 := by
    simpa [FormulaWidthAtMost,
      EmbeddedClause.WidthAtMost] using
      drawingPlanarSATFormula_widthAtMostThree
        formula sourceWidth
  intro translate
  rw [planarSATFiniteAssignmentAt_restrict formula]
  exact PlanarOneInThree.formula_sound
    (drawingPlanarSATFormula formula)
    finiteWidth
    (planarOneInThreeFiniteAssignmentAt
      formula assignment translate)
    (finiteOneInThreeHolds translate)

/-- The periodic positioned Figure 9 replacement preserves satisfiability
exactly relative to the routed planar SAT presentation. -/
theorem drawingPeriodicPlanarOneInThreeFormula_satisfiable_iff_planarSAT
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingPeriodicPlanarOneInThreeFormula formula) ↔
      (drawingPeriodicPlanarSATFormula formula).Satisfiable := by
  constructor
  · rintro ⟨assignment, oneInThreeHolds⟩
    exact
      ⟨restrictPeriodicPlanarOneInThreeAssignment assignment,
        drawingPeriodicPlanarSATFormula_satisfies_of_oneInThree
          formula sourceWidth assignment oneInThreeHolds⟩
  · rintro ⟨assignment, planarHolds⟩
    exact
      ⟨extendPeriodicPlanarOneInThreeAssignment formula assignment,
        drawingPeriodicPlanarOneInThreeFormula_satisfies_of_planarSAT
          formula sourceWidth assignment planarHolds⟩

/-- End-to-end semantic equivalence from an occurrence-three width-three
periodic CNF source to the genuine periodic positioned exact-one formula. -/
theorem drawingPeriodicPlanarOneInThreeFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3)
    (occurrences : formula.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingPeriodicPlanarOneInThreeFormula formula) ↔
      formula.Satisfiable := by
  exact
    (drawingPeriodicPlanarOneInThreeFormula_satisfiable_iff_planarSAT
      formula sourceWidth).trans
      (drawingPeriodicPlanarSATFormula_satisfiable_iff
        formula occurrences)

end PeriodicOrthocrossing
end LeanTrominoes
