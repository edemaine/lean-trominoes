import LeanTrominoes.PeriodicEightOccurrenceSplitOccurrences
import LeanTrominoes.PeriodicThreeSATThreeOrdered
import Mathlib.Tactic.IntervalCases

/-!
# Assigning ordered occurrences to the eight compass ports

An occurrence order supplies the rotation system around every source
variable.  When each such list has length at most eight, its list index
selects a distinct clockwise port of the fixed Figure 7 ring.

This file makes that selection total on arbitrary clause/literal indices and
proves that every genuine tagged occurrence receives a collision-free port.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

/-- Clockwise compass port with a total fallback beyond the eight valid
indices. -/
def portOfIndex : Nat → Port
  | 0 => .northwest
  | 1 => .north
  | 2 => .northeast
  | 3 => .east
  | 4 => .southeast
  | 5 => .south
  | 6 => .southwest
  | _ => .west

/-- The eight valid indices select pairwise different ports. -/
theorem portOfIndex_injective_of_lt
    {first second : Nat}
    (firstLt : first < 8) (secondLt : second < 8)
    (portsEqual : portOfIndex first = portOfIndex second) :
    first = second := by
  interval_cases first <;>
    interval_cases second <;>
    simp_all [portOfIndex]

/-- Look up a literal at a clause/literal presentation position. -/
def literalAt {Variable : Type*}
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    Option (PeriodicLiteral Variable) :=
  source.clauses[clauseIndex]?.bind fun clause =>
    clause[literalIndex]?

/-- Tagged occurrence membership recovers the nested source lookup. -/
theorem literalAt_eq_some_of_tagged_mem
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (tagged :
      PeriodicLiteral Variable × Nat × Nat)
    (taggedMember :
      tagged ∈ taggedLiterals source) :
    literalAt source tagged.2.1 tagged.2.2 =
      some tagged.1 := by
  simp only [taggedLiterals, List.mem_flatMap,
    List.mem_map] at taggedMember
  rcases taggedMember with
    ⟨taggedClause, clauseMember, taggedLiteral,
      literalMember, taggedEqual⟩
  subst tagged
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [literalAt, clauseLookup, literalLookup]

/-- Every genuine occurrence list of the chosen rotation system fits into
the fixed eight compass slots. -/
def FitsEightSlots
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source) : Prop :=
  ∀ atom, (order.copies atom).length ≤ 8

/-- Assign a genuine occurrence copy the port at its position in the chosen
rotation order. -/
def orderedOccurrencePort
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (occurrence : ThreeOccurrenceVariable Variable) : Port :=
  portOfIndex
    ((order.copies occurrence.1).idxOf occurrence)

/-- Total clause/literal-indexed port assignment induced by an occurrence
order.  Invalid indices use the harmless northwest fallback. -/
def occurrencePortsOfOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source) :
    OccurrencePorts where
  port clauseIndex literalIndex :=
    match literalAt source clauseIndex literalIndex with
    | none => .northwest
    | some literal =>
        orderedOccurrencePort order
          (literal.atom, clauseIndex, literalIndex)

/-- On a genuine tagged occurrence, total lookup reduces to its position in
the selected rotation order. -/
theorem occurrencePortsOfOrder_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (tagged :
      PeriodicLiteral Variable × Nat × Nat)
    (taggedMember : tagged ∈ taggedLiterals source) :
    (occurrencePortsOfOrder source order).port
        tagged.2.1 tagged.2.2 =
      orderedOccurrencePort order
        (tagged.1.atom, tagged.2.1, tagged.2.2) := by
  simp [occurrencePortsOfOrder,
    literalAt_eq_some_of_tagged_mem
      source tagged taggedMember]

/-- Equality of fixed copies recovers both the source atom and compass
port. -/
theorem copy_eq_iff
    {Variable : Type*}
    {firstAtom secondAtom : Variable}
    {firstPort secondPort : Port} :
    copy firstAtom firstPort =
        copy secondAtom secondPort ↔
      firstAtom = secondAtom ∧
        firstPort = secondPort := by
  constructor
  · intro equal
    constructor
    · exact congrArg Prod.fst equal
    · apply portIndex_injective
      exact congrArg (fun occurrence => occurrence.2.1) equal
  · rintro ⟨rfl, rfl⟩
    rfl

/-- `idxOf` is injective on values that occur in the indexed list. -/
theorem idxOf_injective_on
    {Element : Type*} [BEq Element] [LawfulBEq Element]
    (elements : List Element)
    {first second : Element}
    (firstMember : first ∈ elements)
    (secondMember : second ∈ elements)
    (indicesEqual :
      elements.idxOf first = elements.idxOf second) :
    first = second := by
  have firstLookup :=
    List.getElem?_idxOf firstMember
  have secondLookup :=
    List.getElem?_idxOf secondMember
  rw [indicesEqual, secondLookup] at firstLookup
  exact Option.some.inj firstLookup.symm

/-- A fitting occurrence order assigns distinct output copies to distinct
tagged source occurrences. -/
theorem occurrencePortsOfOrder_collisionFree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (fits : FitsEightSlots order) :
    (occurrencePortsOfOrder source order).CollisionFree
      source := by
  unfold OccurrencePorts.CollisionFree selectedCopies
  have taggedNodup :
      (taggedLiterals source).Nodup := by
    apply List.Nodup.of_map
      (fun tagged =>
        (tagged.1.atom, tagged.2.1, tagged.2.2))
    simpa [allOccurrenceVariables] using
      allOccurrenceVariables_nodup source
  apply List.Nodup.map_on
    (l := taggedLiterals source) ?_ taggedNodup
  intro first firstMember second secondMember copiesEqual
  rw [occurrencePortsOfOrder_eq source order
      first firstMember,
    occurrencePortsOfOrder_eq source order
      second secondMember] at copiesEqual
  have atomEqual :
      first.1.atom = second.1.atom :=
    (copy_eq_iff.mp copiesEqual).1
  have portEqual :
      orderedOccurrencePort order
          (first.1.atom, first.2.1, first.2.2) =
        orderedOccurrencePort order
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
    (List.idxOf_lt_length_of_mem firstOrderedMember).trans_le
      (fits first.1.atom)
  have secondIndexLt :
      (order.copies second.1.atom).idxOf
          secondOccurrence < 8 :=
    (List.idxOf_lt_length_of_mem secondOrderedMember).trans_le
      (fits second.1.atom)
  have indexEqual :
      (order.copies first.1.atom).idxOf firstOccurrence =
        (order.copies second.1.atom).idxOf secondOccurrence := by
    apply portOfIndex_injective_of_lt
      firstIndexLt secondIndexLt
    simpa [orderedOccurrencePort,
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
