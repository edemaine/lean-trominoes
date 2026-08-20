/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedGreenDegree
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMDegree

/-! # Constructor classifier for degree-three green elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMGreenElementDegreeThree
    (source : PeriodicCNF RoutedVariable) :
    GreenElement RoutedVariable → Bool
  | .ordinaryInternal _ _ _ => false
  | .fixedRedInternal _ _ _ => false
  | .clauseInternal _ => true
  | .clauseTerminal clauseIndex group =>
      (terminalOccurrenceEnumeration source clauseIndex group).length == 1

theorem horizontalThreeDMGreenElement_degree_eq_three_iff
    (source : PeriodicCNF RoutedVariable)
    (element : GreenElement RoutedVariable)
    (elementMember : element ∈ greenElements source) :
    ((problem source).greenIncidences element).length = 3 ↔
      horizontalThreeDMGreenElementDegreeThree source element = true := by
  simp only [greenElements, List.mem_append,
    List.mem_flatMap] at elementMember
  rcases elementMember with variableMember | clauseMember
  · rcases variableMember with
      ⟨atom, atomMember, slot, slotMember, localMember⟩
    cases kindEq : occurrenceConnectorKind source atom slot with
    | fixedRed =>
        simp [occurrenceGreenElements, kindEq] at localMember
        rcases localMember with rfl | rfl | rfl
        · simp [horizontalThreeDMGreenElementDegreeThree,
            (fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.1 .leftRung]
        · simp [horizontalThreeDMGreenElementDegreeThree,
            (fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.1 .topRightLink]
        · simp [horizontalThreeDMGreenElementDegreeThree,
            (fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.1 .bottomRightLink]
    | fixedGreen =>
        simp [occurrenceGreenElements, kindEq] at localMember
        subst element
        have degreeEq :
            ((problem source).greenIncidences
              (.ordinaryInternal atom slot .cycleShared)).length = 2 := by
          simpa [ordinaryGreenPrivate] using
            (ordinaryPrivate_degrees source atom atomMember
              slot slotMember .fixedGreen kindEq).1
        simp [horizontalThreeDMGreenElementDegreeThree, degreeEq]
    | fixedBlue =>
        simp [occurrenceGreenElements, kindEq] at localMember
        subst element
        have degreeEq :
            ((problem source).greenIncidences
              (.ordinaryInternal atom slot .cycleShared)).length = 2 := by
          simpa [ordinaryGreenPrivate] using
            (ordinaryPrivate_degrees source atom atomMember
              slot slotMember .fixedBlue kindEq).1
        simp [horizontalThreeDMGreenElementDegreeThree, degreeEq]
  · rcases clauseMember with
      ⟨clauseIndex, indexMember, localMember⟩
    have indexLt := List.mem_range.mp indexMember
    simp only [List.mem_singleton, List.mem_map] at localMember
    rcases localMember with rfl | ⟨group, _groupMember, rfl⟩
    · simp [horizontalThreeDMGreenElementDegreeThree,
        (clauseInternal_degrees source clauseIndex indexLt).2.1]
    · rw [problem_greenIncidences_clauseTerminal_length
          source clauseIndex indexLt group]
      simp [horizontalThreeDMGreenElementDegreeThree]

end PeriodicCNFStripReduction
end LeanTrominoes
