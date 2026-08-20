/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexSelectedBlueScan

/-! # Clause-only degree-three blue elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMBlueClauseElementsComputed
    (source : PeriodicCNF Nat) : List (BlueElement RoutedVariable) :=
  let typed := horizontalThreeDMTypedSourceComputed source
  (List.range typed.clauses.length).flatMap fun clauseIndex =>
    [.clauseInternal clauseIndex] ++
      allTerminalGroups.map (BlueElement.clauseTerminal clauseIndex)

theorem horizontalThreeDMBlueElementDegreeThree_filter_eq_clause
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMBlueElementsComputed source).filter
        (horizontalThreeDMBlueElementDegreeThree
          (horizontalThreeDMTypedSourceComputed source)) =
      (horizontalThreeDMBlueClauseElementsComputed source).filter
        (horizontalThreeDMBlueElementDegreeThree
          (horizontalThreeDMTypedSourceComputed source)) := by
  let typed := horizontalThreeDMTypedSourceComputed source
  let variableElements :=
    (occurringVariables typed).flatMap fun atom =>
      (usedSlots typed atom).flatMap fun slot =>
        occurrenceBlueElements typed atom slot
  have variableFilter :
      variableElements.filter
          (horizontalThreeDMBlueElementDegreeThree typed) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro element member
    rcases List.mem_flatMap.mp member with
      ⟨atom, _atomMember, slotMember⟩
    rcases List.mem_flatMap.mp slotMember with
      ⟨slot, _slotMember, localMember⟩
    cases kindEq : occurrenceConnectorKind typed atom slot with
    | fixedRed =>
        simp [occurrenceBlueElements, kindEq] at localMember
        rcases localMember with rfl | rfl | rfl <;>
          simp [horizontalThreeDMBlueElementDegreeThree]
    | fixedGreen =>
        simp [occurrenceBlueElements, kindEq] at localMember
        subst element
        simp [horizontalThreeDMBlueElementDegreeThree]
    | fixedBlue =>
        simp [occurrenceBlueElements, kindEq] at localMember
        subst element
        simp [horizontalThreeDMBlueElementDegreeThree]
  change
    (variableElements ++ horizontalThreeDMBlueClauseElementsComputed source).filter
        (horizontalThreeDMBlueElementDegreeThree typed) = _
  rw [List.filter_append, variableFilter, List.nil_append]

end PeriodicCNFStripReduction
end LeanTrominoes
