/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMEncodingComputability

/-!
# Degree bounds after natural-number periodic 3DM encoding

The first-index encoding preserves each colored incidence list up to
permutation.  Consequently, the typed degree-two-or-three invariant transfers
to the natural-number `PeriodicThreeDM` presentation.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Encoding preserves the red degree of every listed typed element. -/
theorem encodedProblem_red_degree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : RedElement Variable)
    (atomMember : atom ∈ redElements source) :
    (encodedProblem source).degree .red
        ((redElements source).idxOf atom) =
      ((problem source).redIncidences atom).length := by
  have incidencePerm :=
    encode_incidences_perm
      (problem source) (redElements source)
      (fun triple => (tripleReferences source triple).red)
      .red
      (by intro triple; rfl)
      (fun triple tripleMember =>
        (problem_isWellFormed source
          triple tripleMember).1)
      (triples_nodup source) atom atomMember
  simpa [PeriodicThreeDM.degree, encodedProblem, problem,
    referenceIncidences,
    TypedPeriodicThreeDM.redIncidences] using
      incidencePerm.length_eq

/-- Encoding preserves the green degree of every listed typed element. -/
theorem encodedProblem_green_degree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : GreenElement Variable)
    (atomMember : atom ∈ greenElements source) :
    (encodedProblem source).degree .green
        ((greenElements source).idxOf atom) =
      ((problem source).greenIncidences atom).length := by
  have incidencePerm :=
    encode_incidences_perm
      (problem source) (greenElements source)
      (fun triple => (tripleReferences source triple).green)
      .green
      (by intro triple; rfl)
      (fun triple tripleMember =>
        (problem_isWellFormed source
          triple tripleMember).2.1)
      (triples_nodup source) atom atomMember
  simpa [PeriodicThreeDM.degree, encodedProblem, problem,
    referenceIncidences,
    TypedPeriodicThreeDM.greenIncidences] using
      incidencePerm.length_eq

/-- Encoding preserves the blue degree of every listed typed element. -/
theorem encodedProblem_blue_degree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : BlueElement Variable)
    (atomMember : atom ∈ blueElements source) :
    (encodedProblem source).degree .blue
        ((blueElements source).idxOf atom) =
      ((problem source).blueIncidences atom).length := by
  have incidencePerm :=
    encode_incidences_perm
      (problem source) (blueElements source)
      (fun triple => (tripleReferences source triple).blue)
      .blue
      (by intro triple; rfl)
      (fun triple tripleMember =>
        (problem_isWellFormed source
          triple tripleMember).2.2)
      (triples_nodup source) atom atomMember
  simpa [PeriodicThreeDM.degree, encodedProblem, problem,
    referenceIncidences,
    TypedPeriodicThreeDM.blueIncidences] using
      incidencePerm.length_eq

/-- Natural-number encoding preserves the degree-two-or-three invariant. -/
theorem encodedProblem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (degree : (problem source).DegreeTwoOrThree) :
    (encodedProblem source).DegreeTwoOrThree := by
  intro color atom atomLt
  cases color with
  | red =>
      have indexLt :
          atom < (redElements source).length := by
        simpa [encodedProblem, TypedPeriodicThreeDM.encode,
          PeriodicThreeDM.elementCount, problem] using atomLt
      let typedAtom := (redElements source)[atom]'indexLt
      have atomMember : typedAtom ∈ redElements source :=
        List.getElem_mem indexLt
      have indexEq :
          (redElements source).idxOf typedAtom = atom :=
        (redElements_nodup source).idxOf_getElem atom indexLt
      rw [← indexEq,
        encodedProblem_red_degree
          source typedAtom atomMember]
      exact degree.1 typedAtom atomMember
  | green =>
      have indexLt :
          atom < (greenElements source).length := by
        simpa [encodedProblem, TypedPeriodicThreeDM.encode,
          PeriodicThreeDM.elementCount, problem] using atomLt
      let typedAtom := (greenElements source)[atom]'indexLt
      have atomMember : typedAtom ∈ greenElements source :=
        List.getElem_mem indexLt
      have indexEq :
          (greenElements source).idxOf typedAtom = atom :=
        (greenElements_nodup source).idxOf_getElem atom indexLt
      rw [← indexEq,
        encodedProblem_green_degree
          source typedAtom atomMember]
      exact degree.2.1 typedAtom atomMember
  | blue =>
      have indexLt :
          atom < (blueElements source).length := by
        simpa [encodedProblem, TypedPeriodicThreeDM.encode,
          PeriodicThreeDM.elementCount, problem] using atomLt
      let typedAtom := (blueElements source)[atom]'indexLt
      have atomMember : typedAtom ∈ blueElements source :=
        List.getElem_mem indexLt
      have indexEq :
          (blueElements source).idxOf typedAtom = atom :=
        (blueElements_nodup source).idxOf_getElem atom indexLt
      rw [← indexEq,
        encodedProblem_blue_degree
          source typedAtom atomMember]
      exact degree.2.2 typedAtom atomMember

/-- The complete unit-free reduction has natural-number degree two or three. -/
theorem unitFreeEncodedProblem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (width : source.WidthAtMost 3) :
    (unitFreeEncodedProblem source).DegreeTwoOrThree := by
  exact encodedProblem_degreeTwoOrThree
    (PeriodicOneInThreeNoUnits.formula source)
    (unitFree_problem_degreeTwoOrThree
      source occurrences width)

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
