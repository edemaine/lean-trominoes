/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMEncodedSatisfiability

/-!
# Correctness of the unit-free exact-one to periodic 3DM reduction

The paired-port clause gadget requires arity two or three.  Composing the
unit-elimination formula with the encoded 3DM construction supplies that
invariant, preserves the occurrence-three bound, and preserves
satisfiability exactly.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- The complete natural-number periodic 3DM output for an exact-one source,
including elimination of empty and unit clauses. -/
def unitFreeEncodedProblem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    PeriodicThreeDM :=
  encodedProblem (PeriodicOneInThreeNoUnits.formula source)

/-- Unit elimination turns a width-three source into clauses of arity two or
three. -/
theorem unitFree_arityTwoOrThree
    {Variable : Type*} (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (PeriodicOneInThreeNoUnits.formula source) := by
  exact
    PeriodicOneInThreeNoUnits.formula_arityTwoOrThree
      source width

/-- Unit elimination preserves the occurrence-three bound under the
decidable-equality Boolean equality used by the 3DM construction. -/
theorem unitFree_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3) :
    @PeriodicCNF.OccurrencesAtMost
      (OneInThreeNoUnitVariable Variable)
      instBEqOfDecidableEq (by infer_instance) 3
      (PeriodicOneInThreeNoUnits.formula source) := by
  have generatedOccurrences :=
    PeriodicOneInThreeNoUnits.formula_occurrencesAtMostThree
      source occurrences
  exact
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (PeriodicOneInThreeNoUnits.formula source)
      generatedOccurrences

/-- The typed unit-free construction has degree two or three. -/
theorem unitFree_problem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (width : source.WidthAtMost 3) :
    (problem
      (PeriodicOneInThreeNoUnits.formula source)).DegreeTwoOrThree := by
  exact problem_degreeTwoOrThree
    (PeriodicOneInThreeNoUnits.formula source)
    (unitFree_occurrencesAtMostThree source occurrences)
    (unitFree_arityTwoOrThree source width)

/-- The fully encoded unit-free 3DM output is satisfiable exactly when the
source exact-one instance is satisfiable. -/
theorem unitFreeEncodedProblem_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3) :
    (unitFreeEncodedProblem source).Satisfiable ↔
      PeriodicOneInThree.Satisfiable source := by
  unfold unitFreeEncodedProblem
  exact
    (encodedProblem_satisfiable_iff_source
      (PeriodicOneInThreeNoUnits.formula source)
      (unitFree_occurrencesAtMostThree
        source occurrences)).trans
      (PeriodicOneInThreeNoUnits.satisfiable_iff source)

/-- The abstract trichromatic orientation of the fully encoded unit-free
output is equivalent to source exact-one satisfiability. -/
theorem unitFreeEncodedProblem_hasOrientation_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3) :
    (unitFreeEncodedProblem source).HasOrientation ↔
      PeriodicOneInThree.Satisfiable source := by
  exact
    (PeriodicThreeDM.satisfiable_iff_hasOrientation
      (unitFreeEncodedProblem source)).symm.trans
        (unitFreeEncodedProblem_satisfiable_iff
          source occurrences)

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
