import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMMatching

/-!
# Source truth values at assembled clause terminals

The total clause-terminal signal reads source literal positions zero, one,
and two.  Thus a binary clause contributes its two literal truth values and
an unused `false` right terminal, while a ternary clause contributes all
three literal truth values.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/-- Membership in the tagged source-occurrence list recovers the nested
literal lookup used by `sourceTerminalSignal`. -/
theorem literalAt_eq_some_of_tagged_mem
    {Variable : Type*} (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    literalAt source tagged.2.1 tagged.2.2 = some tagged.1 := by
  simp only [PeriodicThreeSATThree.taggedLiterals,
    List.mem_flatMap, List.mem_map] at member
  rcases member with
    ⟨taggedClause, clauseMember, taggedLiteral,
      literalMember, taggedEq⟩
  subst tagged
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [literalAt, clauseLookup, literalLookup]

/-- A terminal whose literal position is a genuine tagged occurrence reads
that occurrence's source truth value. -/
theorem sourceTerminalSignal_eq_literalTruth_of_tagged_mem
    {Variable : Type*} (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source)
    (group : X3CClauseTerminalGroup)
    (indexEq :
      literalIndexOfTerminalGroup group = tagged.2.2) :
    sourceTerminalSignal source assignment cell tagged.2.1 group =
      PeriodicOneInThree.literalTruth
        assignment cell tagged.1 := by
  simp [sourceTerminalSignal, indexEq,
    literalAt_eq_some_of_tagged_mem source tagged member]

/-- A satisfied binary or ternary source clause gives an exact-one
three-terminal pattern, with the unused right terminal false in the binary
case. -/
theorem sourceTerminalSignals_exactlyOne
    {Variable : Type*} (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds assignment cell clause) :
    PeriodicOneInThree.ExactlyOne
      [sourceTerminalSignal source assignment cell clauseIndex .top,
        sourceTerminalSignal source assignment cell clauseIndex .left,
        sourceTerminalSignal source assignment cell clauseIndex .right] := by
  rcases clause with _ | ⟨first, tail⟩
  · simp at arity
  rcases tail with _ | ⟨second, tail⟩
  · simp at arity
  rcases tail with _ | ⟨third, tail⟩
  · simpa [sourceTerminalSignal, literalAt,
      literalIndexOfTerminalGroup,
      PeriodicOneInThree.ClauseHolds,
      PeriodicOneInThree.clauseValues,
      PeriodicOneInThree.literalTruth,
      PeriodicOneInThree.ExactlyOne,
      List.count_cons,
      clauseLookup] using sourceHolds
  · have tailEmpty : tail = [] := by
      have tailLength : tail.length = 0 := by
        rcases arity with lengthTwo | lengthThree
        · simp at lengthTwo
        · simpa using lengthThree
      exact List.length_eq_zero_iff.mp tailLength
    subst tail
    simpa [sourceTerminalSignal, literalAt,
      literalIndexOfTerminalGroup,
      PeriodicOneInThree.ClauseHolds,
      PeriodicOneInThree.clauseValues,
      PeriodicOneInThree.literalTruth,
      PeriodicOneInThree.ExactlyOne,
      clauseLookup] using sourceHolds

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
