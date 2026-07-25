import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNodup

/-!
# Natural-number encoding of the planar typed 3DM assembly

Each declared color class and the triple list is duplicate-free, so its
list positions provide faithful natural-number names for the standard
`PeriodicThreeDM` interface.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Number a typed reference by its element's first list position. -/
def encodeReference {Element : Type*} [DecidableEq Element]
    (elements : List Element) (reference : Reference Element) :
    PeriodicThreeDMReference :=
  ⟨elements.idxOf reference.atom, reference.offset⟩

/-- Number the three references of one typed prototype triple. -/
def TypedProblem.encodeTriple
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (triple : Triple Variable) : PeriodicThreeDMTriple :=
  let references := typed.references triple
  ⟨encodeReference typed.redElements references.red,
    encodeReference typed.greenElements references.green,
    encodeReference typed.blueElements references.blue⟩

/-- Compile a typed presentation to the standard natural-number interface. -/
def TypedProblem.encode
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable) : PeriodicThreeDM where
  redCount := typed.redElements.length
  greenCount := typed.greenElements.length
  blueCount := typed.blueElements.length
  triples := typed.triples.map typed.encodeTriple

private theorem encodeTriple_red_lt
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable) (triple : Triple Variable)
    (member :
      (typed.references triple).red.atom ∈ typed.redElements) :
    (typed.encodeTriple triple).red.atom <
      typed.redElements.length := by
  simpa [TypedProblem.encodeTriple, encodeReference] using
    List.idxOf_lt_length_iff.mpr member

private theorem encodeTriple_green_lt
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable) (triple : Triple Variable)
    (member :
      (typed.references triple).green.atom ∈ typed.greenElements) :
    (typed.encodeTriple triple).green.atom <
      typed.greenElements.length := by
  simpa [TypedProblem.encodeTriple, encodeReference] using
    List.idxOf_lt_length_iff.mpr member

private theorem encodeTriple_blue_lt
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable) (triple : Triple Variable)
    (member :
      (typed.references triple).blue.atom ∈ typed.blueElements) :
    (typed.encodeTriple triple).blue.atom <
      typed.blueElements.length := by
  simpa [TypedProblem.encodeTriple, encodeReference] using
    List.idxOf_lt_length_iff.mpr member

/-- Typed well-formedness makes every numbered reference in range. -/
theorem TypedProblem.encode_isWellFormed
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (wellFormed : typed.IsWellFormed) :
    typed.encode.IsWellFormed := by
  intro encodedTriple encodedMember color
  simp only [TypedProblem.encode, List.mem_map] at encodedMember
  rcases encodedMember with ⟨triple, tripleMember, rfl⟩
  have references := wellFormed triple tripleMember
  cases color with
  | red => exact encodeTriple_red_lt typed triple references.1
  | green => exact encodeTriple_green_lt typed triple references.2.1
  | blue => exact encodeTriple_blue_lt typed triple references.2.2

/-- The numbered planar reduction output. -/
def encodedProblem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : PeriodicThreeDM :=
  (problem source).encode

/-- Every numbered reference of the planar output is valid. -/
theorem encodedProblem_isWellFormed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (encodedProblem source).IsWellFormed :=
  (problem source).encode_isWellFormed
    (problem_isWellFormed source)

/-- Read a typed matching at a numbered triple-list position. -/
def TypedProblem.encodeAssignment
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (assignment : typed.MatchingAssignment) :
    typed.encode.MatchingAssignment :=
  fun tripleIndex cell =>
    (typed.triples[tripleIndex]?.map fun triple =>
      assignment triple cell).getD false

/-- Read a numbered matching at the position of each typed triple. -/
def TypedProblem.decodeAssignment
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (assignment : typed.encode.MatchingAssignment) :
    typed.MatchingAssignment :=
  fun triple cell => assignment (typed.triples.idxOf triple) cell

@[simp]
theorem TypedProblem.encodeAssignment_idxOf
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (assignment : typed.MatchingAssignment)
    (triple : Triple Variable) (member : triple ∈ typed.triples)
    (cell : Cell) :
    typed.encodeAssignment assignment
        (typed.triples.idxOf triple) cell =
      assignment triple cell := by
  simp [TypedProblem.encodeAssignment,
    List.getElem?_idxOf member]

@[simp]
theorem TypedProblem.decode_encodeAssignment
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (assignment : typed.MatchingAssignment)
    (triple : Triple Variable) (member : triple ∈ typed.triples)
    (cell : Cell) :
    typed.decodeAssignment (typed.encodeAssignment assignment)
        triple cell =
      assignment triple cell :=
  typed.encodeAssignment_idxOf assignment triple member cell

@[simp]
theorem TypedProblem.encode_decodeAssignment
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (triplesNodup : typed.triples.Nodup)
    (assignment : typed.encode.MatchingAssignment)
    (tripleIndex : Nat) (indexLt : tripleIndex < typed.triples.length)
    (cell : Cell) :
    typed.encodeAssignment (typed.decodeAssignment assignment)
        tripleIndex cell =
      assignment tripleIndex cell := by
  simp [TypedProblem.encodeAssignment,
    TypedProblem.decodeAssignment,
    List.getElem?_eq_getElem indexLt,
    triplesNodup.idxOf_getElem tripleIndex indexLt]

/-- `idxOf` is injective on elements that occur in a list. -/
theorem idxOf_injective_on
    {Element : Type*} [DecidableEq Element]
    (elements : List Element)
    {first second : Element} (firstMember : first ∈ elements)
    (secondMember : second ∈ elements) :
    elements.idxOf first = elements.idxOf second ↔ first = second :=
  PeriodicOneInThreeToThreeDM.idxOf_injective_on
    elements firstMember secondMember

/-- Numbered references agree exactly when their listed typed atoms agree. -/
theorem encodeReference_atom_eq_iff
    {Element : Type*} [DecidableEq Element]
    (elements : List Element)
    (first second : Reference Element)
    (firstMember : first.atom ∈ elements)
    (secondMember : second.atom ∈ elements) :
    (encodeReference elements first).atom =
        (encodeReference elements second).atom ↔
      first.atom = second.atom :=
  idxOf_injective_on elements firstMember secondMember

@[simp]
theorem encodeReference_offset
    {Element : Type*} [DecidableEq Element]
    (elements : List Element) (reference : Reference Element) :
    (encodeReference elements reference).offset =
      reference.offset := by
  rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
