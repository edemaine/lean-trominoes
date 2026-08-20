/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexSelectedRedScan

/-! # Clause-only degree-three red elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMRedClauseElementsComputed
    (source : PeriodicCNF Nat) : List (RedElement RoutedVariable) :=
  let typed := horizontalThreeDMTypedSourceComputed source
  (List.range typed.clauses.length).flatMap fun clauseIndex =>
    [.clauseInternal clauseIndex] ++
      allTerminalGroups.map (RedElement.clauseTerminal clauseIndex)

theorem horizontalThreeDMRedElementDegreeThree_filter_eq_clause
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMRedElementsComputed source).filter
        (horizontalThreeDMRedElementDegreeThree
          (horizontalThreeDMTypedSourceComputed source)) =
      (horizontalThreeDMRedClauseElementsComputed source).filter
        (horizontalThreeDMRedElementDegreeThree
          (horizontalThreeDMTypedSourceComputed source)) := by
  let typed := horizontalThreeDMTypedSourceComputed source
  let variableElements :=
    (occurringVariables typed).flatMap fun atom =>
      (usedSlots typed atom).flatMap fun slot =>
        occurrenceRedElements typed atom slot
  have variableFilter :
      variableElements.filter
          (horizontalThreeDMRedElementDegreeThree typed) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro element member
    rcases List.mem_flatMap.mp member with
      ⟨atom, _atomMember, slotMember⟩
    rcases List.mem_flatMap.mp slotMember with
      ⟨slot, _slotMember, localMember⟩
    cases kindEq : occurrenceConnectorKind typed atom slot with
    | fixedRed =>
        simp [occurrenceRedElements, kindEq] at localMember
        rcases localMember with rfl | rfl | rfl <;>
          simp [horizontalThreeDMRedElementDegreeThree]
    | fixedGreen =>
        simp [occurrenceRedElements, kindEq] at localMember
        subst element
        simp [horizontalThreeDMRedElementDegreeThree]
    | fixedBlue =>
        simp [occurrenceRedElements, kindEq] at localMember
        subst element
        simp [horizontalThreeDMRedElementDegreeThree]
  change
    (variableElements ++ horizontalThreeDMRedClauseElementsComputed source).filter
        (horizontalThreeDMRedElementDegreeThree typed) = _
  rw [List.filter_append, variableFilter, List.nil_append]

end PeriodicCNFStripReduction
end LeanTrominoes
