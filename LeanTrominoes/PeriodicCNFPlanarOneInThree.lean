/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarPeriodicization
import LeanTrominoes.PeriodicCNFPlanarWidth
import LeanTrominoes.PlanarOneInThree

/-!
# Periodicizing the positioned planar exact-one block

The finite routed SAT block is replaced clause-by-clause by Figure 9.  As in
the preceding CNF periodicization, explicit translations of original routed
variables become literal offsets.  Clause-local exact-one auxiliaries are
already scoped inside one finite block, so they become proto-variables at
offset zero.

The semantic bridge is exact at every lattice translate: periodic exact-one
satisfaction is precisely satisfaction of the finite positioned Figure 9
formula under the induced finite assignment.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Proto-variables of the periodic positioned exact-one formula.  The left
summand contains normalized routed SAT variables; the right summand contains
one block-local Figure 9 auxiliary. -/
abbrev PeriodicPlanarOneInThreeVariable (Variable : Type*) :=
  Sum (PeriodicPlanarSATVariable Variable)
    ((Nat × PeriodicClause (PlanarSATVariable Variable)) ×
      OneInThreeAux)

/-- The finite positioned exact-one replacement of the complete routed SAT
block. -/
def drawingPlanarOneInThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List
      (EmbeddedClause
        (OneInThreeVariable (PlanarSATVariable Variable))) :=
  PlanarOneInThree.formula
    (drawingPlanarSATFormula formula)

/-- Normalize a finite Figure 9 variable into a periodic proto-variable and
literal offset. -/
def normalizePlanarOneInThreeVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (inputVariable :
      OneInThreeVariable (PlanarSATVariable Variable)) :
    PeriodicPlanarOneInThreeVariable Variable × Cell :=
  match inputVariable with
  | .inl original =>
      let normalized := normalizePlanarSATVariable formula original
      (.inl normalized.1, normalized.2)
  | .inr auxiliary =>
      (.inr auxiliary, (0, 0))

/-- Periodicize one literal of the positioned exact-one block. -/
def periodicizePlanarOneInThreeLiteral
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal :
      OneInThreeVariable (PlanarSATVariable Variable) × Bool) :
    PeriodicLiteral
      (PeriodicPlanarOneInThreeVariable Variable) :=
  let normalized :=
    normalizePlanarOneInThreeVariable formula literal.1
  ⟨normalized.1, normalized.2, literal.2⟩

/-- Periodicize one positioned exact-one clause. -/
def periodicizePlanarOneInThreeClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      EmbeddedClause
        (OneInThreeVariable (PlanarSATVariable Variable))) :
    PeriodicClause
      (PeriodicPlanarOneInThreeVariable Variable) :=
  clause.literals.map (periodicizePlanarOneInThreeLiteral formula)

/-- The genuine periodic exact-one formula obtained from the routed planar
SAT block and the positioned Figure 9 replacement. -/
def drawingPeriodicPlanarOneInThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF
      (PeriodicPlanarOneInThreeVariable Variable) :=
  ⟨(drawingPlanarOneInThreeFormula formula).map
    (periodicizePlanarOneInThreeClause formula)⟩

/-- Restrict a plane-wide periodic exact-one assignment to the explicit
variables of one translated finite Figure 9 block. -/
def planarOneInThreeFiniteAssignmentAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarOneInThreeVariable Variable →
        Cell → Bool)
    (translate : Cell) :
    OneInThreeVariable (PlanarSATVariable Variable) → Bool :=
  fun inputVariable =>
    let normalized :=
      normalizePlanarOneInThreeVariable formula inputVariable
    assignment normalized.1
      (Cell.add translate normalized.2)

/-- Periodicizing one positioned exact-one clause preserves its truth value
under the induced finite assignment. -/
theorem periodicizePlanarOneInThreeClause_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarOneInThreeVariable Variable →
        Cell → Bool)
    (translate : Cell)
    (clause :
      EmbeddedClause
        (OneInThreeVariable (PlanarSATVariable Variable))) :
    PeriodicOneInThree.ClauseHolds assignment translate
        (periodicizePlanarOneInThreeClause formula clause) ↔
      PlanarOneInThree.ClauseHolds
        (planarOneInThreeFiniteAssignmentAt
          formula assignment translate)
        clause := by
  simp [PeriodicOneInThree.ClauseHolds,
    PeriodicOneInThree.clauseValues,
    PlanarOneInThree.ClauseHolds,
    periodicizePlanarOneInThreeClause,
    periodicizePlanarOneInThreeLiteral,
    planarOneInThreeFiniteAssignmentAt,
    List.map_map, Function.comp_def]

/-- Periodicizing an arbitrary positioned exact-one formula is equivalent to
satisfying that finite formula independently at every translate. -/
theorem periodicizePlanarOneInThreeFormula_satisfies_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (finiteFormula :
      List
        (EmbeddedClause
          (OneInThreeVariable (PlanarSATVariable Variable))))
    (assignment :
      PeriodicPlanarOneInThreeVariable Variable →
        Cell → Bool) :
    PeriodicOneInThree.Satisfies
        ⟨finiteFormula.map
          (periodicizePlanarOneInThreeClause formula)⟩
        assignment ↔
      ∀ translate,
        PlanarOneInThree.FormulaHolds
          (planarOneInThreeFiniteAssignmentAt
            formula assignment translate)
          finiteFormula := by
  constructor
  · intro satisfies translate clause clauseMem
    apply
      (periodicizePlanarOneInThreeClause_holds_iff
        formula assignment translate clause).mp
    exact satisfies translate
      (periodicizePlanarOneInThreeClause formula clause)
      (List.mem_map.mpr ⟨clause, clauseMem, rfl⟩)
  · intro finiteHolds translate periodicClause
      periodicClauseMem
    rcases List.mem_map.mp periodicClauseMem with
      ⟨clause, clauseMem, periodicClauseEq⟩
    subst periodicClause
    apply
      (periodicizePlanarOneInThreeClause_holds_iff
        formula assignment translate clause).mpr
    exact finiteHolds translate clause clauseMem

/-- Exact per-translate semantics of the genuine periodic positioned
exact-one formula. -/
theorem drawingPeriodicPlanarOneInThreeFormula_satisfies_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarOneInThreeVariable Variable →
        Cell → Bool) :
    PeriodicOneInThree.Satisfies
        (drawingPeriodicPlanarOneInThreeFormula formula)
        assignment ↔
      ∀ translate,
        PlanarOneInThree.FormulaHolds
          (planarOneInThreeFiniteAssignmentAt
            formula assignment translate)
          (drawingPlanarOneInThreeFormula formula) := by
  exact periodicizePlanarOneInThreeFormula_satisfies_iff
    formula (drawingPlanarOneInThreeFormula formula) assignment

end PeriodicOrthocrossing
end LeanTrominoes
