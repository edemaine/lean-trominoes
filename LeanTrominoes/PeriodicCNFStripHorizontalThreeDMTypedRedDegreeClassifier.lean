/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedRedDegree
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMDegree

/-! # Constructor classifier for degree-three red elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

/-- Variable-module red elements have degree two.  A clause internal has
degree three, while a terminal has degree three exactly when one variable
occurrence is attached to it. -/
def horizontalThreeDMRedElementDegreeThree
    (source : PeriodicCNF RoutedVariable) :
    RedElement RoutedVariable → Bool
  | .cycleLink _ _ => false
  | .fixedRedInternal _ _ _ => false
  | .clauseInternal _ => true
  | .clauseTerminal clauseIndex group =>
      (terminalOccurrenceEnumeration source clauseIndex group).length == 1

theorem horizontalThreeDMRedElement_degree_eq_three_iff
    (source : PeriodicCNF RoutedVariable)
    (element : RedElement RoutedVariable)
    (elementMember : element ∈ redElements source) :
    ((problem source).redIncidences element).length = 3 ↔
      horizontalThreeDMRedElementDegreeThree source element = true := by
  simp only [redElements, List.mem_append,
    List.mem_flatMap] at elementMember
  rcases elementMember with variableMember | clauseMember
  · rcases variableMember with
      ⟨atom, atomMember, slot, slotMember, localMember⟩
    cases kindEq : occurrenceConnectorKind source atom slot with
    | fixedRed =>
        simp [occurrenceRedElements, kindEq] at localMember
        rcases localMember with rfl | rfl | rfl
        · simp [horizontalThreeDMRedElementDegreeThree,
            problem_redIncidences_cycleLink_length
              source atom atomMember slot slotMember]
        · simp [horizontalThreeDMRedElementDegreeThree,
            (fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).1 .middleRung]
        · simp [horizontalThreeDMRedElementDegreeThree,
            (fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).1 .topAuxiliary]
    | fixedGreen =>
        simp [occurrenceRedElements, kindEq] at localMember
        subst element
        simp [horizontalThreeDMRedElementDegreeThree,
          problem_redIncidences_cycleLink_length
            source atom atomMember slot slotMember]
    | fixedBlue =>
        simp [occurrenceRedElements, kindEq] at localMember
        subst element
        simp [horizontalThreeDMRedElementDegreeThree,
          problem_redIncidences_cycleLink_length
            source atom atomMember slot slotMember]
  · rcases clauseMember with
      ⟨clauseIndex, indexMember, localMember⟩
    have indexLt := List.mem_range.mp indexMember
    simp only [List.mem_singleton, List.mem_map] at localMember
    rcases localMember with rfl | ⟨group, _groupMember, rfl⟩
    · simp [horizontalThreeDMRedElementDegreeThree,
        (clauseInternal_degrees source clauseIndex indexLt).1]
    · rw [problem_redIncidences_clauseTerminal_length
          source clauseIndex indexLt group]
      simp [horizontalThreeDMRedElementDegreeThree]

end PeriodicCNFStripReduction
end LeanTrominoes
