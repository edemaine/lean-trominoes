import LeanTrominoes.PeriodicThreeSATThreeAngularOrder

/-!
# Sortedness of arbitrary terminal-ray angular orders

The semantic occurrence split uses stable merge sort with
`terminalVectorAngleLE`.  Its permutation theorem alone is enough for the
Boolean reduction, but the geometric fan also needs the resulting list to
follow the actual cyclic order.

This file proves that the integer cross-product comparator is total and
transitive.  The only substantive step is transitivity inside one half-plane.
If the middle vector is not on the boundary ray, the identity

`b.y * cross(a,c) = cross(a,b) * c.y + a.y * cross(b,c)`

transports the two assumed signs to the desired sign.  Boundary rays are
handled separately.  The generic merge-sort theorem then gives pairwise
angular sortedness of every extracted occurrence list.
-/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Cross-product order is transitive among nonzero vectors in the
east-to-west half-plane. -/
private theorem terminalVectorCross_transitive_upper
    {first second third : Cell}
    (firstNonzero : first ≠ (0, 0))
    (secondNonzero : second ≠ (0, 0))
    (firstUpper : terminalVectorUpperHalf first = true)
    (secondUpper : terminalVectorUpperHalf second = true)
    (thirdUpper : terminalVectorUpperHalf third = true)
    (firstSecond :
      0 ≤ terminalVectorCross first second)
    (secondThird :
      0 ≤ terminalVectorCross second third) :
    0 ≤ terminalVectorCross first third := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases third with ⟨thirdX, thirdY⟩
  simp only [terminalVectorUpperHalf, decide_eq_true_eq] at firstUpper secondUpper thirdUpper
  simp only [terminalVectorCross] at firstSecond secondThird ⊢
  have firstYNonnegative : 0 ≤ firstY := by
    omega
  have secondYNonnegative : 0 ≤ secondY := by
    omega
  have thirdYNonnegative : 0 ≤ thirdY := by
    omega
  by_cases secondBoundary : secondY = 0
  · have secondXPositive : 0 < secondX := by
      rcases secondUpper with secondPositive | secondAxis
      · omega
      · have secondXNonzero : secondX ≠ 0 := by
          intro secondXZero
          apply secondNonzero
          simp [secondXZero, secondBoundary]
        omega
    have firstYTimesSecondXZero :
        firstY * secondX = 0 := by
      have productNonnegative :
          0 ≤ firstY * secondX :=
        mul_nonneg firstYNonnegative secondXPositive.le
      rw [secondBoundary] at firstSecond
      nlinarith
    have firstYZero : firstY = 0 :=
      (mul_eq_zero.mp firstYTimesSecondXZero).resolve_right
        secondXPositive.ne'
    have firstXPositive : 0 < firstX := by
      rcases firstUpper with firstPositive | firstAxis
      · omega
      · have firstXNonzero : firstX ≠ 0 := by
          intro firstXZero
          apply firstNonzero
          simp [firstXZero, firstYZero]
        omega
    rw [firstYZero]
    simpa using
      mul_nonneg firstXPositive.le thirdYNonnegative
  · have secondYPositive : 0 < secondY := by
      omega
    have weightedIdentity :
        secondY *
            (firstX * thirdY - firstY * thirdX) =
          (firstX * secondY - firstY * secondX) * thirdY +
            firstY *
              (secondX * thirdY - secondY * thirdX) := by
      ring
    have rightNonnegative :
        0 ≤
          (firstX * secondY - firstY * secondX) * thirdY +
            firstY *
              (secondX * thirdY - secondY * thirdX) :=
      add_nonneg
        (mul_nonneg firstSecond thirdYNonnegative)
        (mul_nonneg firstYNonnegative secondThird)
    nlinarith

/-- Cross-product order is transitive among nonzero vectors in the
west-to-east complementary half-plane. -/
private theorem terminalVectorCross_transitive_lower
    {first second third : Cell}
    (firstNonzero : first ≠ (0, 0))
    (secondNonzero : second ≠ (0, 0))
    (firstLower : terminalVectorUpperHalf first = false)
    (secondLower : terminalVectorUpperHalf second = false)
    (thirdLower : terminalVectorUpperHalf third = false)
    (firstSecond :
      0 ≤ terminalVectorCross first second)
    (secondThird :
      0 ≤ terminalVectorCross second third) :
    0 ≤ terminalVectorCross first third := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases third with ⟨thirdX, thirdY⟩
  simp only [terminalVectorUpperHalf, decide_eq_false_iff_not,
    not_or, not_and, not_lt, not_le] at firstLower secondLower thirdLower
  simp only [terminalVectorCross] at firstSecond secondThird ⊢
  have firstYNonpositive : firstY ≤ 0 := by
    omega
  have secondYNonpositive : secondY ≤ 0 := by
    omega
  have thirdYNonpositive : thirdY ≤ 0 := by
    omega
  by_cases secondBoundary : secondY = 0
  · have secondXNegative : secondX < 0 := by
      have secondXNonzero : secondX ≠ 0 := by
        intro secondXZero
        apply secondNonzero
        simp [secondXZero, secondBoundary]
      omega
    have firstYTimesSecondXZero :
        firstY * secondX = 0 := by
      have productNonnegative :
          0 ≤ firstY * secondX :=
        mul_nonneg_of_nonpos_of_nonpos
          firstYNonpositive secondXNegative.le
      rw [secondBoundary] at firstSecond
      nlinarith
    have firstYZero : firstY = 0 :=
      (mul_eq_zero.mp firstYTimesSecondXZero).resolve_right
        secondXNegative.ne
    have firstXNegative : firstX < 0 := by
      have firstXNonzero : firstX ≠ 0 := by
        intro firstXZero
        apply firstNonzero
        simp [firstXZero, firstYZero]
      omega
    rw [firstYZero]
    simpa using
      mul_nonneg_of_nonpos_of_nonpos
        firstXNegative.le thirdYNonpositive
  · have secondYNegative : secondY < 0 := by
      omega
    have weightedIdentity :
        secondY *
            (firstX * thirdY - firstY * thirdX) =
          (firstX * secondY - firstY * secondX) * thirdY +
            firstY *
              (secondX * thirdY - secondY * thirdX) := by
      ring
    have rightNonpositive :
        (firstX * secondY - firstY * secondX) * thirdY +
            firstY *
              (secondX * thirdY - secondY * thirdX) ≤ 0 :=
      add_nonpos
        (mul_nonpos_of_nonneg_of_nonpos
          firstSecond thirdYNonpositive)
        (mul_nonpos_of_nonpos_of_nonneg
          firstYNonpositive secondThird)
    nlinarith

/-- The polar-angle comparator is transitive on all integer vectors,
including its zero-vector fallback. -/
theorem terminalVectorAngleLE_transitive
    (first second third : Cell)
    (firstSecond :
      terminalVectorAngleLE first second = true)
    (secondThird :
      terminalVectorAngleLE second third = true) :
    terminalVectorAngleLE first third = true := by
  by_cases firstZero : first = (0, 0)
  · subst first
    simp [terminalVectorAngleLE] at firstSecond
    subst second
    exact secondThird
  by_cases secondZero : second = (0, 0)
  · subst second
    simp [terminalVectorAngleLE] at secondThird
    subst third
    simp [terminalVectorAngleLE, firstZero]
  by_cases thirdZero : third = (0, 0)
  · subst third
    simp [terminalVectorAngleLE, firstZero]
  cases firstUpper :
      terminalVectorUpperHalf first <;>
    cases secondUpper :
      terminalVectorUpperHalf second <;>
    cases thirdUpper :
      terminalVectorUpperHalf third
  all_goals
    simp [terminalVectorAngleLE, firstZero,
      secondZero, thirdZero, firstUpper,
      secondUpper, thirdUpper] at firstSecond secondThird ⊢
  · exact
      terminalVectorCross_transitive_lower
        firstZero secondZero firstUpper secondUpper
        thirdUpper firstSecond secondThird
  · exact
      terminalVectorCross_transitive_upper
        firstZero secondZero firstUpper secondUpper
        thirdUpper firstSecond secondThird

/-- Any two integer terminal vectors are comparable in at least one angular
direction. -/
theorem terminalVectorAngleLE_total
    (first second : Cell) :
    (terminalVectorAngleLE first second ||
        terminalVectorAngleLE second first) = true := by
  by_cases firstZero : first = (0, 0)
  · subst first
    simp [terminalVectorAngleLE]
  by_cases secondZero : second = (0, 0)
  · subst second
    simp [terminalVectorAngleLE, firstZero]
  cases firstUpper :
      terminalVectorUpperHalf first <;>
    cases secondUpper :
      terminalVectorUpperHalf second
  all_goals
    simp [terminalVectorAngleLE, firstZero,
      secondZero, firstUpper, secondUpper,
      terminalVectorCross] <;> ring_nf <;> omega

/-- Boolean occurrence comparison inherits transitivity from terminal
vectors. -/
theorem occurrenceAngleLE_transitive
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second third : ThreeOccurrenceVariable Variable)
    (firstSecond :
      occurrenceAngleLE routes first second = true)
    (secondThird :
      occurrenceAngleLE routes second third = true) :
    occurrenceAngleLE routes first third = true :=
  terminalVectorAngleLE_transitive
    (occurrenceTerminalVector routes first)
    (occurrenceTerminalVector routes second)
    (occurrenceTerminalVector routes third)
    firstSecond secondThird

/-- Boolean occurrence comparison is total. -/
theorem occurrenceAngleLE_total
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second : ThreeOccurrenceVariable Variable) :
    (occurrenceAngleLE routes first second ||
        occurrenceAngleLE routes second first) = true :=
  terminalVectorAngleLE_total
    (occurrenceTerminalVector routes first)
    (occurrenceTerminalVector routes second)

/-- The angular occurrence list is genuinely sorted by the same arbitrary
terminal-ray comparator used to construct it. -/
theorem angularOccurrenceVariables_pairwise
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (angularOccurrenceVariables source routes atom).Pairwise
      (fun first second =>
        occurrenceAngleLE routes first second = true) := by
  unfold angularOccurrenceVariables
  exact
    List.pairwise_mergeSort
      (le := occurrenceAngleLE routes)
      (occurrenceAngleLE_transitive routes)
      (occurrenceAngleLE_total routes)
      (occurrenceVariables source atom)

end PeriodicThreeSATThree
end LeanTrominoes
