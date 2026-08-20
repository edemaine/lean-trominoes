/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexSelectedGreenScan

/-! # Clause-only degree-three green elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMGreenClauseElementsComputed
    (source : PeriodicCNF Nat) : List (GreenElement RoutedVariable) :=
  let typed := horizontalThreeDMTypedSourceComputed source
  (List.range typed.clauses.length).flatMap fun clauseIndex =>
    [.clauseInternal clauseIndex] ++
      allTerminalGroups.map (GreenElement.clauseTerminal clauseIndex)

theorem horizontalThreeDMGreenElementDegreeThree_filter_eq_clause
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMGreenElementsComputed source).filter
        (horizontalThreeDMGreenElementDegreeThree
          (horizontalThreeDMTypedSourceComputed source)) =
      (horizontalThreeDMGreenClauseElementsComputed source).filter
        (horizontalThreeDMGreenElementDegreeThree
          (horizontalThreeDMTypedSourceComputed source)) := by
  let typed := horizontalThreeDMTypedSourceComputed source
  let variableElements :=
    (occurringVariables typed).flatMap fun atom =>
      (usedSlots typed atom).flatMap fun slot =>
        occurrenceGreenElements typed atom slot
  have variableFilter :
      variableElements.filter
          (horizontalThreeDMGreenElementDegreeThree typed) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro element member
    rcases List.mem_flatMap.mp member with
      ⟨atom, _atomMember, slotMember⟩
    rcases List.mem_flatMap.mp slotMember with
      ⟨slot, _slotMember, localMember⟩
    cases kindEq : occurrenceConnectorKind typed atom slot with
    | fixedRed =>
        simp [occurrenceGreenElements, kindEq] at localMember
        rcases localMember with rfl | rfl | rfl <;>
          simp [horizontalThreeDMGreenElementDegreeThree]
    | fixedGreen =>
        simp [occurrenceGreenElements, kindEq] at localMember
        subst element
        simp [horizontalThreeDMGreenElementDegreeThree]
    | fixedBlue =>
        simp [occurrenceGreenElements, kindEq] at localMember
        subst element
        simp [horizontalThreeDMGreenElementDegreeThree]
  change
    (variableElements ++ horizontalThreeDMGreenClauseElementsComputed source).filter
        (horizontalThreeDMGreenElementDegreeThree typed) = _
  rw [List.filter_append, variableFilter, List.nil_append]

end PeriodicCNFStripReduction
end LeanTrominoes
