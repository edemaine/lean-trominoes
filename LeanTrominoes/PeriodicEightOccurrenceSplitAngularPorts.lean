import LeanTrominoes.PeriodicEightOccurrenceSplitPortAssignment

/-!
# East-first compass ports for angular occurrence orders

`terminalVectorAngleLE` enumerates rays counterclockwise from east (with the
screen-coordinate convention used by the drawing).  The original generic
port assignment enumerates Figure 7 from northwest, which preserves cyclic
order but introduces an unnecessary fixed rotation.

This module supplies the geometrically aligned enumeration

`east, southeast, south, southwest, west, northwest, north, northeast`.

Collinear occurrences remain adjacent because the angular sort is stable.
As with the generic enumeration, every fitting order receives distinct
ports, so fixed-eight splitting retains its degree-three bound.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

/-- Compass slots in the same cyclic order and with the same starting ray as
`terminalVectorAngleLE`. -/
def angularPortOfIndex : Nat → Port
  | 0 => .east
  | 1 => .southeast
  | 2 => .south
  | 3 => .southwest
  | 4 => .west
  | 5 => .northwest
  | 6 => .north
  | _ => .northeast

/-- The eight valid angular indices select pairwise different ports. -/
theorem angularPortOfIndex_injective_of_lt
    {first second : Nat}
    (firstLt : first < 8) (secondLt : second < 8)
    (portsEqual :
      angularPortOfIndex first = angularPortOfIndex second) :
    first = second := by
  interval_cases first <;>
    interval_cases second <;>
    simp_all [angularPortOfIndex]

/-- Assign a genuine occurrence the east-first compass port at its position
in an angular order. -/
def angularOrderedOccurrencePort
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (occurrence : ThreeOccurrenceVariable Variable) : Port :=
  angularPortOfIndex
    ((order.copies occurrence.1).idxOf occurrence)

/-- Total clause/literal-indexed east-first assignment induced by an
occurrence order. -/
def occurrencePortsOfAngularOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source) :
    OccurrencePorts where
  port clauseIndex literalIndex :=
    match literalAt source clauseIndex literalIndex with
    | none => .east
    | some literal =>
        angularOrderedOccurrencePort order
          (literal.atom, clauseIndex, literalIndex)

/-- On a genuine tagged occurrence, total lookup reduces to its east-first
index in the chosen angular order. -/
theorem occurrencePortsOfAngularOrder_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (tagged : PeriodicLiteral Variable × Nat × Nat)
    (taggedMember : tagged ∈ taggedLiterals source) :
    (occurrencePortsOfAngularOrder source order).port
        tagged.2.1 tagged.2.2 =
      angularOrderedOccurrencePort order
        (tagged.1.atom, tagged.2.1, tagged.2.2) := by
  simp [occurrencePortsOfAngularOrder,
    literalAt_eq_some_of_tagged_mem
      source tagged taggedMember]

/-- A fitting angular order assigns distinct east-first output copies to
distinct tagged source occurrences. -/
theorem occurrencePortsOfAngularOrder_collisionFree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (fits : FitsEightSlots order) :
    (occurrencePortsOfAngularOrder
      source order).CollisionFree source := by
  unfold OccurrencePorts.CollisionFree selectedCopies
  apply List.Nodup.map_on
    (l := taggedLiterals source) ?_
      (taggedLiterals_nodup source)
  intro first firstMember second secondMember copiesEqual
  rw [occurrencePortsOfAngularOrder_eq source order
      first firstMember,
    occurrencePortsOfAngularOrder_eq source order
      second secondMember] at copiesEqual
  have atomEqual :
      first.1.atom = second.1.atom :=
    (copy_eq_iff.mp copiesEqual).1
  have portEqual :
      angularOrderedOccurrencePort order
          (first.1.atom, first.2.1, first.2.2) =
        angularOrderedOccurrencePort order
          (second.1.atom, second.2.1, second.2.2) :=
    (copy_eq_iff.mp copiesEqual).2
  let firstOccurrence :
      ThreeOccurrenceVariable Variable :=
    (first.1.atom, first.2.1, first.2.2)
  let secondOccurrence :
      ThreeOccurrenceVariable Variable :=
    (second.1.atom, second.2.1, second.2.2)
  have firstOriginalMember :
      firstOccurrence ∈
        occurrenceVariables source first.1.atom :=
    occurrenceVariables_mem source firstMember
  have secondOriginalMember :
      secondOccurrence ∈
        occurrenceVariables source second.1.atom :=
    occurrenceVariables_mem source secondMember
  have firstOrderedMember :
      firstOccurrence ∈ order.copies first.1.atom :=
    (order.mem_iff first.1.atom firstOccurrence).mpr
      firstOriginalMember
  have secondOrderedMember :
      secondOccurrence ∈ order.copies second.1.atom :=
    (order.mem_iff second.1.atom secondOccurrence).mpr
      secondOriginalMember
  have firstIndexLt :
      (order.copies first.1.atom).idxOf
          firstOccurrence < 8 :=
    (List.idxOf_lt_length_of_mem
      firstOrderedMember).trans_le (fits first.1.atom)
  have secondIndexLt :
      (order.copies second.1.atom).idxOf
          secondOccurrence < 8 :=
    (List.idxOf_lt_length_of_mem
      secondOrderedMember).trans_le (fits second.1.atom)
  have indexEqual :
      (order.copies first.1.atom).idxOf firstOccurrence =
        (order.copies second.1.atom).idxOf secondOccurrence := by
    apply angularPortOfIndex_injective_of_lt
      firstIndexLt secondIndexLt
    simpa [angularOrderedOccurrencePort,
      firstOccurrence, secondOccurrence] using portEqual
  have secondOrderedMember' :
      secondOccurrence ∈ order.copies first.1.atom := by
    simpa [atomEqual] using secondOrderedMember
  have occurrenceEqual :
      firstOccurrence = secondOccurrence :=
    idxOf_injective_on
      (order.copies first.1.atom)
      firstOrderedMember secondOrderedMember'
      (by simpa [atomEqual] using indexEqual)
  have clauseIndexEqual :
      first.2.1 = second.2.1 :=
    congrArg (fun occurrence => occurrence.2.1)
      occurrenceEqual
  have literalIndexEqual :
      first.2.2 = second.2.2 :=
    congrArg (fun occurrence => occurrence.2.2)
      occurrenceEqual
  have literalEqual :
      first.1 = second.1 := by
    have firstLookup :=
      literalAt_eq_some_of_tagged_mem
        source first firstMember
    have secondLookup :=
      literalAt_eq_some_of_tagged_mem
        source second secondMember
    rw [clauseIndexEqual, literalIndexEqual,
      secondLookup] at firstLookup
    exact Option.some.inj firstLookup.symm
  exact Prod.ext literalEqual
    (Prod.ext clauseIndexEqual literalIndexEqual)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
