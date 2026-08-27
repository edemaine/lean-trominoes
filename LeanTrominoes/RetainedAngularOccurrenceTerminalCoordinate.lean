/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularTerminalDataProfile
import LeanTrominoes.RetainedTerminalDirectionEnumeration
import Mathlib.Data.Prod.Lex

/-! # Numeric coordinates for retained angular occurrences -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- The finite angular rank followed by the radial primitive-block length.
This is the exact lexicographic key used by the retained angular occurrence
order on certified terminal rays. -/
def retainedOccurrenceTerminalCoordinate
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copy : ThreeOccurrenceVariable Variable) : Nat ×ₗ Nat :=
  let terminal := classifiedRetainedTerminalData
    (occurrenceTerminalVector routes copy)
  toLex (terminal.1.angularRank, terminal.2)

/-- On two certified retained terminal rays, the geometric angular-radial
comparison is exactly lexicographic comparison of the finite direction rank
and radial length. -/
theorem occurrenceAngleLE_eq_decide_terminalCoordinateLE
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second : ThreeOccurrenceVariable Variable)
    (firstRetained :
      RetainedTerminalRayVector
        (occurrenceTerminalVector routes first))
    (secondRetained :
      RetainedTerminalRayVector
        (occurrenceTerminalVector routes second)) :
    occurrenceAngleLE routes first second =
      decide
        (retainedOccurrenceTerminalCoordinate routes first ≤
          retainedOccurrenceTerminalCoordinate routes second) := by
  let firstTerminal := classifiedRetainedTerminalData
    (occurrenceTerminalVector routes first)
  let secondTerminal := classifiedRetainedTerminalData
    (occurrenceTerminalVector routes second)
  have firstClassified :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes first) =
        some firstTerminal := by
    exact
      retainedTerminalDirectionClassify_classifiedRetainedTerminalData
        firstRetained
  have secondClassified :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes second) =
        some secondTerminal := by
    exact
      retainedTerminalDirectionClassify_classifiedRetainedTerminalData
        secondRetained
  rcases firstTerminal with ⟨firstDirection, firstLength⟩
  rcases secondTerminal with ⟨secondDirection, secondLength⟩
  have firstTerminalEq :
      classifiedRetainedTerminalData
          (occurrenceTerminalVector routes first) =
        (firstDirection, firstLength) :=
    classifiedRetainedTerminalData_eq_of_classified firstClassified
  have secondTerminalEq :
      classifiedRetainedTerminalData
          (occurrenceTerminalVector routes second) =
        (secondDirection, secondLength) :=
    classifiedRetainedTerminalData_eq_of_classified secondClassified
  unfold retainedOccurrenceTerminalCoordinate
  rw [firstTerminalEq, secondTerminalEq]
  change occurrenceAngleLE routes first second =
    decide
      (toLex (firstDirection.angularRank, firstLength) ≤
        toLex (secondDirection.angularRank, secondLength))
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, Prod.Lex.toLex_le_toLex]
  by_cases ranksEqual :
      firstDirection.angularRank = secondDirection.angularRank
  · have directionsEqual : firstDirection = secondDirection :=
      RetainedTerminalDirection.angularRank_injective ranksEqual
    subst secondDirection
    rw [occurrenceAngleLE_iff_length_le_of_same_direction_classified
      routes first second firstClassified secondClassified]
    simp
  · unfold occurrenceAngleLE terminalVectorAngleRadialLE
    rw [terminalVectorAngleLE_eq_rankLE_of_classified
      firstClassified secondClassified]
    rw [terminalVectorAngleLE_eq_rankLE_of_classified
      secondClassified firstClassified]
    simp only [decide_eq_true_eq]
    omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
