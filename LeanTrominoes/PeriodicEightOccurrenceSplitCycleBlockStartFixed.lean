/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockIndex
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightData

/-! # Fixed-width implication-cycle block starts -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

/-- Every separator-enhanced implication ring has exactly nine clauses. -/
@[simp] theorem cycleClausesFor_length_eq_copiesPerVariable
    {Variable : Type*} (atom : Variable) :
    (cycleClausesFor atom).length =
      PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable := by
  simp [OccurrenceSplitRing.cycleClausesFor_eq_cycleFormula,
    OccurrenceSplitRing.cycleFormula,
    OccurrenceSplitRing.presentedCycleVertices,
    OccurrenceSplitRing.cycleVertices,
    PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable]

/-- In a duplicate-free atom list, the recursive block origin is the fixed
nine-clause width times the atom's stable presentation index. -/
theorem cycleBlockStart_eq_copiesPerVariable_mul_index
    {Variable : Type*} [DecidableEq Variable]
    (atoms : List Variable)
    (atomsNodup : atoms.Nodup)
    {atom : Variable} {atomIndex : Nat}
    (atomMember : (atom, atomIndex) ∈ atoms.zipIdx) :
    cycleBlockStart atoms atom =
      PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable * atomIndex := by
  induction atoms generalizing atomIndex with
  | nil =>
      simp at atomMember
  | cons head rest induction =>
      have nodupParts := List.nodup_cons.mp atomsNodup
      have atomLookup :=
        (List.mem_zipIdx_iff_getElem?).mp atomMember
      cases atomIndex with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq]
            at atomLookup
          subst atom
          simp [cycleBlockStart]
      | succ atomIndex =>
          simp only [List.getElem?_cons_succ] at atomLookup
          have tailMember :
              (atom, atomIndex) ∈ rest.zipIdx :=
            List.mem_zipIdx_iff_getElem?.mpr atomLookup
          have headNe : head ≠ atom := by
            intro headEq
            subst atom
            exact nodupParts.1
              (List.fst_mem_of_mem_zipIdx tailMember)
          rw [cycleBlockStart, if_neg headNe,
            cycleClausesFor_length_eq_copiesPerVariable,
            induction nodupParts.2 tailMember]
          simp [Nat.mul_succ, Nat.add_comm]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
