import LeanTrominoes.PeriodicOneInThreeToThreeDMWellFormed

/-!
# Encoding typed periodic 3DM as natural-number periodic 3DM

The general `PeriodicThreeDM` interface numbers each color class separately.
This file compiles a typed presentation by taking the first index of every
element in its declared color list, then proves that typed well-formedness
makes every resulting index valid.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Number a typed reference by its element's index in a finite color list. -/
def encodeReference {Element : Type*} [DecidableEq Element]
    (elements : List Element) (reference : Reference Element) :
    PeriodicThreeDMReference :=
  ⟨elements.idxOf reference.atom, reference.offset⟩

/-- Number the three colored references of one typed triple. -/
def TypedPeriodicThreeDM.encodeTriple {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (triple : Triple Variable) : PeriodicThreeDMTriple :=
  let references := problem.references triple
  ⟨encodeReference problem.redElements references.red,
    encodeReference problem.greenElements references.green,
    encodeReference problem.blueElements references.blue⟩

/-- Compile a typed finite presentation to the natural-number interface. -/
def TypedPeriodicThreeDM.encode {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable) :
    PeriodicThreeDM where
  redCount := problem.redElements.length
  greenCount := problem.greenElements.length
  blueCount := problem.blueElements.length
  triples := problem.triples.map problem.encodeTriple

/-- A listed encoded red reference is in range. -/
theorem encodeTriple_red_lt {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable)
    (triple : Triple Variable)
    (member : (problem.references triple).red.atom ∈
      problem.redElements) :
    (problem.encodeTriple triple).red.atom <
      problem.redElements.length := by
  simpa [TypedPeriodicThreeDM.encodeTriple, encodeReference] using
    List.idxOf_lt_length_iff.mpr member

/-- A listed encoded green reference is in range. -/
theorem encodeTriple_green_lt {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable)
    (triple : Triple Variable)
    (member : (problem.references triple).green.atom ∈
      problem.greenElements) :
    (problem.encodeTriple triple).green.atom <
      problem.greenElements.length := by
  simpa [TypedPeriodicThreeDM.encodeTriple, encodeReference] using
    List.idxOf_lt_length_iff.mpr member

/-- A listed encoded blue reference is in range. -/
theorem encodeTriple_blue_lt {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable)
    (triple : Triple Variable)
    (member : (problem.references triple).blue.atom ∈
      problem.blueElements) :
    (problem.encodeTriple triple).blue.atom <
      problem.blueElements.length := by
  simpa [TypedPeriodicThreeDM.encodeTriple, encodeReference] using
    List.idxOf_lt_length_iff.mpr member

/-- Encoding preserves well-formedness of every triple reference. -/
theorem TypedPeriodicThreeDM.encode_isWellFormed
    {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable)
    (wellFormed : problem.IsWellFormed) :
    problem.encode.IsWellFormed := by
  intro encodedTriple encodedMember color
  simp only [TypedPeriodicThreeDM.encode, List.mem_map] at encodedMember
  rcases encodedMember with ⟨triple, tripleMember, rfl⟩
  have references := wellFormed triple tripleMember
  cases color with
  | red =>
      exact encodeTriple_red_lt problem triple references.1
  | green =>
      exact encodeTriple_green_lt problem triple references.2.1
  | blue =>
      exact encodeTriple_blue_lt problem triple references.2.2

/-- The concrete natural-number periodic 3DM instance produced from a source
exact-one formula. -/
def encodedProblem {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : PeriodicThreeDM :=
  (problem source).encode

/-- Every reference of the concrete reduction output is in range. -/
theorem encodedProblem_isWellFormed {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (encodedProblem source).IsWellFormed :=
  TypedPeriodicThreeDM.encode_isWellFormed
    (problem source) (problem_isWellFormed source)

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
