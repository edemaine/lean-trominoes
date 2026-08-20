/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedBlueDegree
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMDegree

/-! # Constructor classifier for degree-three blue elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMBlueElementDegreeThree
    (source : PeriodicCNF RoutedVariable) :
    BlueElement RoutedVariable → Bool
  | .ordinaryInternal _ _ _ => false
  | .fixedRedInternal _ _ _ => false
  | .clauseInternal _ => true
  | .clauseTerminal clauseIndex group =>
      (terminalOccurrenceEnumeration source clauseIndex group).length == 1

theorem horizontalThreeDMBlueElement_degree_eq_three_iff
    (source : PeriodicCNF RoutedVariable)
    (element : BlueElement RoutedVariable)
    (elementMember : element ∈ blueElements source) :
    ((problem source).blueIncidences element).length = 3 ↔
      horizontalThreeDMBlueElementDegreeThree source element = true := by
  simp only [blueElements, List.mem_append,
    List.mem_flatMap] at elementMember
  rcases elementMember with variableMember | clauseMember
  · rcases variableMember with
      ⟨atom, atomMember, slot, slotMember, localMember⟩
    cases kindEq : occurrenceConnectorKind source atom slot with
    | fixedRed =>
        simp [occurrenceBlueElements, kindEq] at localMember
        rcases localMember with rfl | rfl | rfl
        · simp [horizontalThreeDMBlueElementDegreeThree,
            (fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.2 .topLeftLink]
        · simp [horizontalThreeDMBlueElementDegreeThree,
            (fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.2 .bottomLeftLink]
        · simp [horizontalThreeDMBlueElementDegreeThree,
            (fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.2 .rightRung]
    | fixedGreen =>
        simp [occurrenceBlueElements, kindEq] at localMember
        subst element
        have degreeEq :
            ((problem source).blueIncidences
              (.ordinaryInternal atom slot .auxiliaryShared)).length = 2 := by
          simpa [ordinaryBluePrivate] using
            (ordinaryPrivate_degrees source atom atomMember
              slot slotMember .fixedGreen kindEq).2
        simp [horizontalThreeDMBlueElementDegreeThree, degreeEq]
    | fixedBlue =>
        simp [occurrenceBlueElements, kindEq] at localMember
        subst element
        have degreeEq :
            ((problem source).blueIncidences
              (.ordinaryInternal atom slot .auxiliaryShared)).length = 2 := by
          simpa [ordinaryBluePrivate] using
            (ordinaryPrivate_degrees source atom atomMember
              slot slotMember .fixedBlue kindEq).2
        simp [horizontalThreeDMBlueElementDegreeThree, degreeEq]
  · rcases clauseMember with
      ⟨clauseIndex, indexMember, localMember⟩
    have indexLt := List.mem_range.mp indexMember
    simp only [List.mem_singleton, List.mem_map] at localMember
    rcases localMember with rfl | ⟨group, _groupMember, rfl⟩
    · simp [horizontalThreeDMBlueElementDegreeThree,
        (clauseInternal_degrees source clauseIndex indexLt).2.2]
    · rw [problem_blueIncidences_clauseTerminal_length
          source clauseIndex indexLt group]
      simp [horizontalThreeDMBlueElementDegreeThree]

end PeriodicCNFStripReduction
end LeanTrominoes
