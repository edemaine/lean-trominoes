import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingCorrectness

/-!
# Satisfiability of the encoded periodic 3DM instance

The colorwise incident-value permutations transport exact cover between the
typed construction and its natural-number `PeriodicThreeDM` encoding.  This
closes the representation boundary and combines with typed correctness to
give source exact-one satisfiability equivalence.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- A typed perfect matching remains a perfect matching after numbering all
prototype triples and elements. -/
theorem encoded_satisfies_of_typed_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (typedSatisfies : (problem source).Satisfies assignment) :
    (encodedProblem source).Satisfies
      ((problem source).encodeAssignment assignment) := by
  intro color atom atomLt cell
  cases color with
  | red =>
      change atom < (redElements source).length at atomLt
      let typedAtom := (redElements source)[atom]
      have atomMember :
          typedAtom ∈ redElements source :=
        List.getElem_mem atomLt
      have indexEq :
          (redElements source).idxOf typedAtom = atom :=
        (redElements_nodup source).idxOf_getElem atom atomLt
      have covered :=
        (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
          (encoded_redIncidentValues_perm
            source assignment typedAtom atomMember cell)).mpr
          (typedSatisfies.1 typedAtom
            (by
              change typedAtom ∈ redElements source
              exact atomMember)
            cell)
      simpa [indexEq] using covered
  | green =>
      change atom < (greenElements source).length at atomLt
      let typedAtom := (greenElements source)[atom]
      have atomMember :
          typedAtom ∈ greenElements source :=
        List.getElem_mem atomLt
      have indexEq :
          (greenElements source).idxOf typedAtom = atom :=
        (greenElements_nodup source).idxOf_getElem atom atomLt
      have covered :=
        (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
          (encoded_greenIncidentValues_perm
            source assignment typedAtom atomMember cell)).mpr
          (typedSatisfies.2.1 typedAtom
            (by
              change typedAtom ∈ greenElements source
              exact atomMember)
            cell)
      simpa [indexEq] using covered
  | blue =>
      change atom < (blueElements source).length at atomLt
      let typedAtom := (blueElements source)[atom]
      have atomMember :
          typedAtom ∈ blueElements source :=
        List.getElem_mem atomLt
      have indexEq :
          (blueElements source).idxOf typedAtom = atom :=
        (blueElements_nodup source).idxOf_getElem atom atomLt
      have covered :=
        (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
          (encoded_blueIncidentValues_perm
            source assignment typedAtom atomMember cell)).mpr
          (typedSatisfies.2.2 typedAtom
            (by
              change typedAtom ∈ blueElements source
              exact atomMember)
            cell)
      simpa [indexEq] using covered

/-- Decoding any numbered perfect matching gives a perfect matching of the
typed presentation. -/
theorem typed_satisfies_of_encoded_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (encodedProblem source).MatchingAssignment)
    (encodedSatisfies :
      (encodedProblem source).Satisfies assignment) :
    (problem source).Satisfies
      ((problem source).decodeAssignment assignment) := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom atomMember cell
    have indexLt :
        (redElements source).idxOf atom <
          (redElements source).length :=
      List.idxOf_lt_length_iff.mpr atomMember
    exact
      (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
        (decoded_redIncidentValues_perm
          source assignment atom atomMember cell)).mp
        (encodedSatisfies .red
          ((redElements source).idxOf atom)
          (by
            change
              (redElements source).idxOf atom <
                (redElements source).length
            exact indexLt)
          cell)
  · intro atom atomMember cell
    have indexLt :
        (greenElements source).idxOf atom <
          (greenElements source).length :=
      List.idxOf_lt_length_iff.mpr atomMember
    exact
      (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
        (decoded_greenIncidentValues_perm
          source assignment atom atomMember cell)).mp
        (encodedSatisfies .green
          ((greenElements source).idxOf atom)
          (by
            change
              (greenElements source).idxOf atom <
                (greenElements source).length
            exact indexLt)
          cell)
  · intro atom atomMember cell
    have indexLt :
        (blueElements source).idxOf atom <
          (blueElements source).length :=
      List.idxOf_lt_length_iff.mpr atomMember
    exact
      (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
        (decoded_blueIncidentValues_perm
          source assignment atom atomMember cell)).mp
        (encodedSatisfies .blue
          ((blueElements source).idxOf atom)
          (by
            change
              (blueElements source).idxOf atom <
                (blueElements source).length
            exact indexLt)
          cell)

/-- Typed and natural-number presentations admit perfect matchings
simultaneously. -/
theorem encodedProblem_satisfiable_iff_typed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (encodedProblem source).Satisfiable ↔
      (problem source).Satisfiable := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨(problem source).decodeAssignment assignment,
        typed_satisfies_of_encoded_satisfies
          source assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨(problem source).encodeAssignment assignment,
        encoded_satisfies_of_typed_satisfies
          source assignment satisfies⟩

/-- The encoded periodic 3DM instance is satisfiable exactly when its
occurrence-three exact-one source is satisfiable. -/
theorem encodedProblem_satisfiable_iff_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    (encodedProblem source).Satisfiable ↔
      PeriodicOneInThree.Satisfiable source := by
  exact
    (encodedProblem_satisfiable_iff_typed source).trans
      (problem_satisfiable_iff source occurrences arity)

/-- Equivalently, the encoded incidence graph has a valid abstract
trichromatic orientation exactly when the source exact-one instance is
satisfiable. -/
theorem encodedProblem_hasOrientation_iff_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    (encodedProblem source).HasOrientation ↔
      PeriodicOneInThree.Satisfiable source := by
  exact
    (PeriodicThreeDM.satisfiable_iff_hasOrientation
      (encodedProblem source)).symm.trans
        (encodedProblem_satisfiable_iff_source
          source occurrences arity)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
