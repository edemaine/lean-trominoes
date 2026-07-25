import LeanTrominoes.PeriodicOneInThreeToThreeDMNodup

/-!
# Assignment transport through the periodic 3DM encoding

Typed triple selections are read at their prototype-list index.  Conversely,
a numbered selection is read at a typed triple's `idxOf`.  These operations
are inverse on all declared triples; the numbered-to-typed-to-numbered
direction uses duplicate-freedom to recover the original list position.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Read a typed assignment by numbered prototype index.  Out-of-range
indices are assigned `false`, though actual encoded incidences are in range. -/
def TypedPeriodicThreeDM.encodeAssignment {Variable : Type*}
    [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment) :
    problem.encode.MatchingAssignment :=
  fun tripleIndex cell =>
    (problem.triples[tripleIndex]?.map fun triple =>
      assignment triple cell).getD false

/-- Read a numbered assignment at each typed triple's prototype index. -/
def TypedPeriodicThreeDM.decodeAssignment {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.encode.MatchingAssignment) :
    problem.MatchingAssignment :=
  fun triple cell => assignment (problem.triples.idxOf triple) cell

/-- Encoding reads a listed typed triple at exactly its `idxOf`. -/
@[simp]
theorem TypedPeriodicThreeDM.encodeAssignment_idxOf
    {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment)
    (triple : Triple Variable) (member : triple ∈ problem.triples)
    (cell : Cell) :
    problem.encodeAssignment assignment
        (problem.triples.idxOf triple) cell =
      assignment triple cell := by
  simp [TypedPeriodicThreeDM.encodeAssignment,
    List.getElem?_idxOf member]

/-- Decoding an encoded typed assignment is the identity on every declared
triple prototype. -/
@[simp]
theorem TypedPeriodicThreeDM.decode_encodeAssignment
    {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment)
    (triple : Triple Variable) (member : triple ∈ problem.triples)
    (cell : Cell) :
    problem.decodeAssignment (problem.encodeAssignment assignment)
        triple cell =
      assignment triple cell := by
  exact problem.encodeAssignment_idxOf
    assignment triple member cell

/-- In a duplicate-free list, the value at an in-range position has that
position as its first index. -/
theorem idxOf_getElem_of_nodup {Element : Type*}
    [DecidableEq Element] (elements : List Element)
    (nodup : elements.Nodup) (index : Nat)
    (indexLt : index < elements.length) :
    elements.idxOf elements[index] = index :=
  nodup.idxOf_getElem index indexLt

/-- Re-encoding a decoded numbered assignment recovers every valid prototype
index when the typed triple list is duplicate-free. -/
@[simp]
theorem TypedPeriodicThreeDM.encode_decodeAssignment
    {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable)
    (triplesNodup : problem.triples.Nodup)
    (assignment : problem.encode.MatchingAssignment)
    (tripleIndex : Nat) (indexLt : tripleIndex < problem.triples.length)
    (cell : Cell) :
    problem.encodeAssignment (problem.decodeAssignment assignment)
        tripleIndex cell =
      assignment tripleIndex cell := by
  simp [TypedPeriodicThreeDM.encodeAssignment,
    TypedPeriodicThreeDM.decodeAssignment,
    List.getElem?_eq_getElem indexLt,
    triplesNodup.idxOf_getElem tripleIndex indexLt]

/-- `idxOf` distinguishes any two values that occur in a list. -/
theorem idxOf_injective_on {Element : Type*} [DecidableEq Element]
    (elements : List Element)
    {first second : Element} (firstMember : first ∈ elements)
    (secondMember : second ∈ elements) :
    elements.idxOf first = elements.idxOf second ↔ first = second := by
  constructor
  · intro indices
    have firstLookup := List.getElem?_idxOf firstMember
    have secondLookup := List.getElem?_idxOf secondMember
    rw [indices, secondLookup] at firstLookup
    exact Option.some.inj firstLookup.symm
  · intro equal
    exact congrArg elements.idxOf equal

/-- Two listed typed references receive the same number exactly when they
name the same element. -/
theorem encodeReference_atom_eq_iff {Element : Type*}
    [DecidableEq Element] (elements : List Element)
    (first second : Reference Element)
    (firstMember : first.atom ∈ elements)
    (secondMember : second.atom ∈ elements) :
    (encodeReference elements first).atom =
        (encodeReference elements second).atom ↔
      first.atom = second.atom := by
  exact idxOf_injective_on elements firstMember secondMember

/-- Encoding never changes a reference's lattice offset. -/
@[simp]
theorem encodeReference_offset {Element : Type*}
    [DecidableEq Element] (elements : List Element)
    (reference : Reference Element) :
    (encodeReference elements reference).offset = reference.offset := by
  rfl

/-- The specialized reduction output inherits both assignment round trips. -/
theorem problem_assignment_roundTrips {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (∀ (assignment : (problem source).MatchingAssignment)
        triple, triple ∈ (problem source).triples → ∀ cell,
      (problem source).decodeAssignment
          ((problem source).encodeAssignment assignment) triple cell =
        assignment triple cell) ∧
      (∀ (assignment : (encodedProblem source).MatchingAssignment)
        tripleIndex, tripleIndex < (problem source).triples.length → ∀ cell,
      (problem source).encodeAssignment
          ((problem source).decodeAssignment assignment) tripleIndex cell =
        assignment tripleIndex cell) := by
  constructor
  · intro assignment triple member cell
    exact (problem source).decode_encodeAssignment
      assignment triple member cell
  · intro assignment tripleIndex indexLt cell
    exact (problem source).encode_decodeAssignment
      (triples_nodup source) assignment tripleIndex indexLt cell

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
