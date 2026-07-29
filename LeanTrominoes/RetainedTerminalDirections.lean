import LeanTrominoes.PeriodicThreeSATThreeAngularOrder
import LeanTrominoes.RetainedRayRasterizationCorridor

/-!
# Terminal directions of retained planar-SAT routes

The retained planar-SAT drawing uses eleven directed slopes.  Eight are the
compass rays, while the routed source-clause star contributes three extra
directions.  Routes are stored from clause to variable, whereas the angular
occurrence order reads the final segment backwards from the variable.

This file packages that reversed finite vocabulary.  Its ranks enumerate the
terminal rays in exactly the east-first order used by
`terminalVectorAngleLE`:

`east, left-arm, southeast, south, right-arm, southwest, west, northwest,
north, northeast, middle-arm`.

The classification and order lemmas below are the finite interface needed by
the local adapter that will replace a retained source vertex by a Figure 7
occurrence-splitting fan.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree
open PlanarThreeSAT

/-- The compass ray opposite a forward clause-to-variable ray. -/
def oppositePort : Port → Port
  | .northwest => .southeast
  | .north => .south
  | .northeast => .southwest
  | .east => .west
  | .southeast => .northwest
  | .south => .north
  | .southwest => .northeast
  | .west => .east

@[simp]
theorem oppositePort_oppositePort (port : Port) :
    oppositePort (oppositePort port) = port := by
  cases port <;> rfl

/-- One of the eleven possible backwards terminal directions at a retained
planar-SAT variable endpoint. -/
inductive RetainedTerminalDirection where
  | compass (port : Port)
  | routedClause (arm : DuplicatorArm)
  deriving DecidableEq, Repr

/-- Primitive backwards vector represented by a retained terminal
direction. -/
def RetainedTerminalDirection.primitive :
    RetainedTerminalDirection → Cell
  | .compass port => port.unitVector
  | .routedClause arm =>
      Cell.sub (0, 0) (routedClauseRayPrimitive arm)

/-- East-first angular rank in the eleven-direction retained vocabulary. -/
def RetainedTerminalDirection.angularRank :
    RetainedTerminalDirection → Nat
  | .compass .east => 0
  | .routedClause .left => 1
  | .compass .southeast => 2
  | .compass .south => 3
  | .routedClause .right => 4
  | .compass .southwest => 5
  | .compass .west => 6
  | .compass .northwest => 7
  | .compass .north => 8
  | .compass .northeast => 9
  | .routedClause .middle => 10

@[simp]
theorem RetainedTerminalDirection.angularRank_lt_eleven
    (direction : RetainedTerminalDirection) :
    direction.angularRank < 11 := by
  cases direction with
  | compass port =>
      cases port <;> decide
  | routedClause arm =>
      cases arm <;> decide

@[simp]
theorem RetainedTerminalDirection.primitive_ne_zero
    (direction : RetainedTerminalDirection) :
    direction.primitive ≠ (0, 0) := by
  cases direction with
  | compass port =>
      exact port.unitVector_ne_zero
  | routedClause arm =>
      cases arm <;>
        decide

/-- Convert a forward retained ray into its backwards terminal direction,
discarding its positive length. -/
def RetainedRay.terminalDirection : RetainedRay →
    RetainedTerminalDirection
  | .compass port _ => .compass (oppositePort port)
  | .routedClause arm _ => .routedClause arm

/-- A vector is a retained terminal ray when its negation is one of the
forward retained-ray displacements. -/
def RetainedTerminalRayVector (vector : Cell) : Prop :=
  RetainedRayVector (Cell.sub (0, 0) vector)

instance (vector : Cell) :
    Decidable (RetainedTerminalRayVector vector) := by
  unfold RetainedTerminalRayVector
  infer_instance

/-- Classify a retained terminal vector, retaining both its direction and
its positive primitive-block length. -/
def retainedTerminalDirectionClassify
    (vector : Cell) :
    Option (RetainedTerminalDirection × Nat) :=
  (retainedRayClassify (Cell.sub (0, 0) vector)).map
    fun ray => (ray.terminalDirection, ray.length)

/-- The terminal classifier succeeds exactly on retained terminal rays. -/
theorem retainedTerminalDirectionClassify_isSome_iff
    (vector : Cell) :
    (retainedTerminalDirectionClassify vector).isSome ↔
      RetainedTerminalRayVector vector := by
  unfold retainedTerminalDirectionClassify
    RetainedTerminalRayVector RetainedRayVector
  cases retainedRayClassify (Cell.sub (0, 0) vector) <;>
    simp

/-- A successful terminal classification has positive length and represents
the input vector exactly. -/
theorem retainedTerminalDirectionClassify_sound
    {vector : Cell}
    {direction : RetainedTerminalDirection}
    {length : Nat}
    (classified :
      retainedTerminalDirectionClassify vector =
        some (direction, length)) :
    0 < length ∧
      vector =
        Cell.scale length direction.primitive := by
  unfold retainedTerminalDirectionClassify at classified
  generalize rayClassified :
      retainedRayClassify (Cell.sub (0, 0) vector) =
        classifiedRay
  cases classifiedRay with
  | none =>
      simp [rayClassified] at classified
  | some ray =>
      simp [rayClassified] at classified
      rcases classified with ⟨rfl, rfl⟩
      have sound := retainedRayClassify_sound rayClassified
      constructor
      · exact sound.1
      · rcases vector with ⟨horizontal, vertical⟩
        cases ray with
        | compass port length =>
            cases port <;>
              simp [RetainedRay.terminalDirection,
                RetainedTerminalDirection.primitive,
                oppositePort, RetainedRay.vector,
                RetainedRay.length, Port.unitVector,
                Cell.scale, Cell.sub]
                at sound ⊢ <;>
              omega
        | routedClause arm length =>
            cases arm <;>
              simp [RetainedRay.terminalDirection,
                RetainedTerminalDirection.primitive,
                RetainedRay.vector, RetainedRay.length,
                routedClauseRayPrimitive, Cell.scale, Cell.sub]
                at sound ⊢ <;>
              omega

/-- Positive scaling preserves whether a vector is zero. -/
private theorem scale_eq_zero_iff
    {factor : Int} (positive : 0 < factor)
    (vector : Cell) :
    Cell.scale factor vector = (0, 0) ↔
      vector = (0, 0) := by
  rcases vector with ⟨horizontal, vertical⟩
  simp only [Cell.scale, Prod.mk.injEq]
  constructor
  · rintro ⟨horizontalZero, verticalZero⟩
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    simp

/-- Positive scaling preserves the east-first comparator's half-plane
partition. -/
private theorem terminalVectorUpperHalf_scale
    {factor : Int} (positive : 0 < factor)
    (vector : Cell) :
    terminalVectorUpperHalf (Cell.scale factor vector) =
      terminalVectorUpperHalf vector := by
  rcases vector with ⟨horizontal, vertical⟩
  apply Bool.eq_iff_iff.mpr
  simp only [terminalVectorUpperHalf, decide_eq_true_eq,
    Cell.scale]
  constructor <;> rintro (verticalPositive | ⟨verticalZero,
      horizontalNonnegative⟩)
  · left
    nlinarith
  · right
    constructor <;> nlinarith
  · left
    exact mul_pos positive verticalPositive
  · right
    constructor
    · simp [verticalZero]
    · exact mul_nonneg positive.le horizontalNonnegative

/-- Scaling the two arguments multiplies their oriented area by the positive
product of the two scale factors. -/
private theorem terminalVectorCross_scale
    (firstFactor secondFactor : Int)
    (first second : Cell) :
    terminalVectorCross
        (Cell.scale firstFactor first)
        (Cell.scale secondFactor second) =
      firstFactor * secondFactor *
        terminalVectorCross first second := by
  rcases first with ⟨firstHorizontal, firstVertical⟩
  rcases second with ⟨secondHorizontal, secondVertical⟩
  simp [terminalVectorCross, Cell.scale]
  ring

/-- Independently changing the positive lengths of two nonzero rays does
not change their angular comparison. -/
private theorem terminalVectorAngleLE_scale
    {firstFactor secondFactor : Int}
    (firstPositive : 0 < firstFactor)
    (secondPositive : 0 < secondFactor)
    (first second : Cell) :
    terminalVectorAngleLE
        (Cell.scale firstFactor first)
        (Cell.scale secondFactor second) =
      terminalVectorAngleLE first second := by
  have productPositive :
      0 < firstFactor * secondFactor :=
    mul_pos firstPositive secondPositive
  by_cases firstZero : first = (0, 0)
  · subst first
    rw [terminalVectorAngleLE,
      if_pos (by simp [Cell.scale]),
      terminalVectorAngleLE, if_pos rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact scale_eq_zero_iff secondPositive second
  by_cases secondZero : second = (0, 0)
  · subst second
    have firstScaledNonzero :
        Cell.scale firstFactor first ≠ (0, 0) :=
      (scale_eq_zero_iff firstPositive first).not.mpr firstZero
    rw [terminalVectorAngleLE, if_neg firstScaledNonzero,
      if_pos (by simp [Cell.scale]),
      terminalVectorAngleLE, if_neg firstZero, if_pos rfl]
  have firstScaledNonzero :
      Cell.scale firstFactor first ≠ (0, 0) :=
    (scale_eq_zero_iff firstPositive first).not.mpr firstZero
  have secondScaledNonzero :
      Cell.scale secondFactor second ≠ (0, 0) :=
    (scale_eq_zero_iff secondPositive second).not.mpr secondZero
  rw [terminalVectorAngleLE, terminalVectorAngleLE]
  simp only [firstZero, secondZero, firstScaledNonzero,
    secondScaledNonzero, if_false,
    terminalVectorUpperHalf_scale firstPositive,
    terminalVectorUpperHalf_scale secondPositive,
    terminalVectorCross_scale]
  split <;> split
  all_goals try rfl
  all_goals
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor <;> intro crossNonnegative
  all_goals nlinarith

/-- The eleven primitive vectors themselves occur in their advertised
east-first rank order. -/
theorem terminalVectorAngleLE_primitive
    (first second : RetainedTerminalDirection) :
    terminalVectorAngleLE first.primitive second.primitive =
      decide (first.angularRank ≤ second.angularRank) := by
  cases first with
  | compass firstPort =>
      cases firstPort <;>
        cases second with
        | compass secondPort =>
            cases secondPort <;> native_decide
        | routedClause secondArm =>
            cases secondArm <;> native_decide
  | routedClause firstArm =>
      cases firstArm <;>
        cases second with
        | compass secondPort =>
            cases secondPort <;> native_decide
        | routedClause secondArm =>
            cases secondArm <;> native_decide

/-- Positive multiples of the eleven primitives are compared exactly by
their finite east-first ranks. -/
theorem terminalVectorAngleLE_scale_primitive
    (first second : RetainedTerminalDirection)
    {firstLength secondLength : Nat}
    (firstPositive : 0 < firstLength)
    (secondPositive : 0 < secondLength) :
    terminalVectorAngleLE
        (Cell.scale firstLength first.primitive)
        (Cell.scale secondLength second.primitive) =
      decide (first.angularRank ≤ second.angularRank) := by
  rw [terminalVectorAngleLE_scale
    (by exact_mod_cast firstPositive)
    (by exact_mod_cast secondPositive)]
  exact terminalVectorAngleLE_primitive first second

/-- Classified positive terminal vectors are ordered by the finite retained
direction ranks. -/
theorem terminalVectorAngleLE_eq_rankLE_of_classified
    {firstVector secondVector : Cell}
    {firstDirection secondDirection : RetainedTerminalDirection}
    {firstLength secondLength : Nat}
    (firstClassified :
      retainedTerminalDirectionClassify firstVector =
        some (firstDirection, firstLength))
    (secondClassified :
      retainedTerminalDirectionClassify secondVector =
        some (secondDirection, secondLength)) :
    terminalVectorAngleLE firstVector secondVector =
      decide
        (firstDirection.angularRank ≤
          secondDirection.angularRank) := by
  have firstSound :=
    retainedTerminalDirectionClassify_sound firstClassified
  have secondSound :=
    retainedTerminalDirectionClassify_sound secondClassified
  rw [firstSound.2, secondSound.2]
  exact terminalVectorAngleLE_scale_primitive
    firstDirection secondDirection
    firstSound.1 secondSound.1

/-- The occurrence comparator used by stable merge sort has the same finite
rank interpretation whenever both selected route terminals are classified. -/
theorem occurrenceAngleLE_eq_rankLE_of_classified
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second : ThreeOccurrenceVariable Variable)
    {firstDirection secondDirection : RetainedTerminalDirection}
    {firstLength secondLength : Nat}
    (firstClassified :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes first) =
        some (firstDirection, firstLength))
    (secondClassified :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes second) =
        some (secondDirection, secondLength)) :
    occurrenceAngleLE routes first second =
      decide
        (firstDirection.angularRank ≤
          secondDirection.angularRank) := by
  unfold occurrenceAngleLE
  exact terminalVectorAngleLE_eq_rankLE_of_classified
    firstClassified secondClassified

/-- The backwards terminal vector of a nondegenerate retained-ray polyline
belongs to the eleven-direction terminal vocabulary. -/
theorem RetainedRayPolyline.routeTerminalVector_retained
    {route : List Cell}
    (retained : RetainedRayPolyline route)
    (routeLength : 2 ≤ route.length) :
    RetainedTerminalRayVector
      (routeTerminalVector route) := by
  have segmentsNonempty :
      gridPolylineSegments route ≠ [] := by
    intro segmentsEmpty
    have segmentsLengthZero :
        (gridPolylineSegments route).length = 0 := by
      rw [segmentsEmpty]
      rfl
    rw [gridPolylineSegments_length] at segmentsLengthZero
    omega
  unfold routeTerminalVector
  generalize lastEq :
      (gridPolylineSegments route).getLast? = lastSegment
  cases lastSegment with
  | none =>
      have : gridPolylineSegments route = [] := by
        simpa using lastEq
      exact (segmentsNonempty this).elim
  | some segment =>
      have segmentMember :
          segment ∈ gridPolylineSegments route :=
        List.mem_of_mem_getLast? (by simpa [lastEq])
      have forwardRetained := retained segment segmentMember
      simpa [RetainedTerminalRayVector, Cell.sub] using
        forwardRetained

end PeriodicEightOccurrenceSplit
end LeanTrominoes
