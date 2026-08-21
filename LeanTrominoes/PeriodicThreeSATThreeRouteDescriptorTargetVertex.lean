/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorData
import LeanTrominoes.PeriodicThreeSATThreeExactFormulaVariableEnumeration

/-! # Target vertex indices after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

private theorem occurrence_idxOf_decidableEq_eq
    {Variable : Type*} [DecidableEq Variable]
    (item : ThreeOccurrenceVariable Variable)
    (items : List (ThreeOccurrenceVariable Variable)) :
    @List.idxOf (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq item items = items.idxOf item := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
      rw [induction]

/-- The variable endpoint of any split-formula route is indexed in the exact
grouped-and-one-step-rotated occurrence-copy order. -/
@[simp] theorem numericRouteDescriptor_formula_targetVertexIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (incidence : CNFIncidence (ThreeOccurrenceVariable Variable))
    (edgeIndex : Nat) :
    (incidence.numericRouteDescriptor
      (formula source) edgeIndex).targetVertexIndex =
        (rotatedOccurrenceVariables source).idxOf
          incidence.literal.atom := by
  simp [CNFIncidence.numericRouteDescriptor,
    formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables]
  exact occurrence_idxOf_decidableEq_eq
    incidence.literal.atom (rotatedOccurrenceVariables source)

end PeriodicThreeSATThree
end LeanTrominoes
