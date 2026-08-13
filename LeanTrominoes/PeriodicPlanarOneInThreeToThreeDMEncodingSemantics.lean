/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncode

/-!
# Semantic transport through natural-number encoding

The typed construction is compiled by numbering every element and triple at
its first position in a duplicate-free prototype list.  This file proves that
the numbered incidence enumerator is a permutation of the corresponding
typed incidence list, then transports exact-cover assignments in both
directions.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Generic typed incidences for one selected color reference. -/
def referenceIncidences {Variable Element : Type*}
    [DecidableEq Element] (problem : TypedProblem Variable)
    (reference : Triple Variable → Reference Element)
    (atom : Element) : List (Incidence Variable) :=
  problem.triples.filterMap fun triple =>
    let current := reference triple
    if current.atom = atom then
      some ⟨triple, current.offset⟩
    else
      none

/-- Number a typed incidence by the prototype index of its triple. -/
def TypedProblem.encodeIncidence {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (incidence : Incidence Variable) : PeriodicThreeDM.Incidence :=
  ⟨problem.triples.idxOf incidence.triple, incidence.offset⟩

/-- Every generic typed incidence names a triple in the presentation. -/
theorem triple_mem_of_mem_referenceIncidences
    {Variable Element : Type*} [DecidableEq Element]
    (problem : TypedProblem Variable)
    (reference : Triple Variable → Reference Element)
    (atom : Element) (incidence : Incidence Variable)
    (member :
      incidence ∈ referenceIncidences problem reference atom) :
    incidence.triple ∈ problem.triples := by
  simp only [referenceIncidences, List.mem_filterMap] at member
  rcases member with ⟨triple, tripleMember, output⟩
  split at output
  · simp only [Option.some.injEq] at output
    subst incidence
    exact tripleMember
  · contradiction

/-- Generic typed incidence enumeration preserves duplicate-freedom of the
triple list. -/
theorem referenceIncidences_nodup
    {Variable Element : Type*} [DecidableEq Element]
    (problem : TypedProblem Variable)
    (reference : Triple Variable → Reference Element)
    (atom : Element) (triplesNodup : problem.triples.Nodup) :
    (referenceIncidences problem reference atom).Nodup := by
  unfold referenceIncidences
  apply List.Nodup.filterMap
  · intro first second incidence firstOutput secondOutput
    dsimp only at firstOutput secondOutput
    split at firstOutput
    · split at secondOutput
      · simp only [Option.mem_def] at firstOutput secondOutput
        have incidenceEq :=
          Option.some.inj
            (firstOutput.trans secondOutput.symm)
        exact congrArg Incidence.triple incidenceEq
      · simp at secondOutput
    · simp at firstOutput
  · exact triplesNodup

/-- Numbering a duplicate-free typed incidence list remains
duplicate-free, provided every incidence names a listed triple. -/
theorem encodeIncidences_nodup
    {Variable : Type*} [DecidableEq Variable]
    (problem : TypedProblem Variable)
    (incidences : List (Incidence Variable))
    (incidencesNodup : incidences.Nodup)
    (triplesListed :
      ∀ incidence ∈ incidences,
        incidence.triple ∈ problem.triples) :
    (incidences.map problem.encodeIncidence).Nodup := by
  induction incidences with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at incidencesNodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro encodedMember
        rcases List.mem_map.mp encodedMember with
          ⟨other, otherMember, encodedEq⟩
        have headListed :=
          triplesListed head (List.mem_cons_self)
        have otherListed :=
          triplesListed other
            (List.mem_cons_of_mem head otherMember)
        have tripleEq : head.triple = other.triple := by
          apply
            (idxOf_injective_on problem.triples
              headListed otherListed).mp
          exact (congrArg
            PeriodicThreeDM.Incidence.tripleIndex
            encodedEq).symm
        have offsetEq : head.offset = other.offset :=
          (congrArg PeriodicThreeDM.Incidence.offset
            encodedEq).symm
        have incidenceEq : head = other := by
          cases head
          cases other
          simp_all
        exact incidencesNodup.1
          (incidenceEq ▸ otherMember)
      · exact induction incidencesNodup.2
          (fun incidence member =>
            triplesListed incidence
              (List.mem_cons_of_mem head member))

/-- The natural-number incidence enumerator never duplicates a triple
prototype index. -/
theorem periodicThreeDM_incidences_nodup
    (problem : PeriodicThreeDM) (color : Gadget.WireColor)
    (atom : Nat) :
    (problem.incidences color atom).Nodup := by
  unfold PeriodicThreeDM.incidences
  apply List.Nodup.filterMap
  · intro first second incidence firstOutput secondOutput
    dsimp only at firstOutput secondOutput
    split at firstOutput
    · split at secondOutput
      · simp only [Option.mem_def] at firstOutput secondOutput
        have incidenceEq :=
          Option.some.inj
            (firstOutput.trans secondOutput.symm)
        have := congrArg
          PeriodicThreeDM.Incidence.tripleIndex
          incidenceEq
        simpa using this
      · simp at secondOutput
    · simp at firstOutput
  · exact List.nodup_range

/-- Membership in a numbered incidence list is equivalent to membership in
the corresponding typed list followed by incidence encoding. -/
theorem mem_encode_incidences_iff
    {Variable Element : Type*}
    [DecidableEq Variable] [DecidableEq Element]
    (problem : TypedProblem Variable)
    (elements : List Element)
    (reference : Triple Variable → Reference Element)
    (color : Gadget.WireColor)
    (referenceEncoded :
      ∀ triple,
        (problem.encodeTriple triple).reference color =
          encodeReference elements (reference triple))
    (referencesListed :
      ∀ triple ∈ problem.triples,
        (reference triple).atom ∈ elements)
    (triplesNodup : problem.triples.Nodup)
    (atom : Element) (atomMember : atom ∈ elements)
    (encodedIncidence : PeriodicThreeDM.Incidence) :
    encodedIncidence ∈
        problem.encode.incidences color (elements.idxOf atom) ↔
      encodedIncidence ∈
        (referenceIncidences problem reference atom).map
          problem.encodeIncidence := by
  constructor
  · intro encodedMember
    simp only [PeriodicThreeDM.incidences,
      List.mem_filterMap] at encodedMember
    rcases encodedMember with
      ⟨tripleIndex, indexMember, output⟩
    have encodedIndexLt :
        tripleIndex < problem.encode.triples.length :=
      List.mem_range.mp indexMember
    have indexLt : tripleIndex < problem.triples.length := by
      simpa [TypedProblem.encode] using encodedIndexLt
    let triple := problem.triples[tripleIndex]
    have tripleMember : triple ∈ problem.triples :=
      List.getElem_mem indexLt
    have encodedAt :
        (problem.encode.triples.getD tripleIndex default) =
          problem.encodeTriple triple := by
      change
        (problem.triples.map problem.encodeTriple).getD
            tripleIndex default =
          problem.encodeTriple triple
      rw [List.getD_eq_getElem
        (l := problem.triples.map problem.encodeTriple)
        (d := default) encodedIndexLt]
      simp [triple]
    split at output
    · rename_i encodedAtomEq
      rw [encodedAt, referenceEncoded] at encodedAtomEq output
      simp only [Option.some.injEq] at output
      subst encodedIncidence
      have atomEq : (reference triple).atom = atom :=
        (encodeReference_atom_eq_iff elements
          (reference triple) ⟨atom, (0, 0)⟩
          (referencesListed triple tripleMember)
          atomMember).mp encodedAtomEq
      apply List.mem_map.mpr
      refine
        ⟨⟨triple, (reference triple).offset⟩,
          ?_, ?_⟩
      · unfold referenceIncidences
        apply List.mem_filterMap.mpr
        exact
          ⟨triple, tripleMember, by simp [atomEq]⟩
      · exact congrArg₂ PeriodicThreeDM.Incidence.mk
          (triplesNodup.idxOf_getElem tripleIndex indexLt)
          rfl
    · simp at output
  · intro encodedMember
    rcases List.mem_map.mp encodedMember with
      ⟨typedIncidence, typedMember, encodedEq⟩
    simp only [referenceIncidences,
      List.mem_filterMap] at typedMember
    rcases typedMember with
      ⟨triple, tripleMember, output⟩
    split at output
    · rename_i atomEq
      simp only [Option.some.injEq] at output
      subst typedIncidence
      subst encodedIncidence
      have indexLt :
          problem.triples.idxOf triple <
            problem.triples.length :=
        List.idxOf_lt_length_iff.mpr tripleMember
      have encodedAt :
          problem.encode.triples.getD
              (problem.triples.idxOf triple) default =
            problem.encodeTriple triple := by
        have encodedIndexLt :
            problem.triples.idxOf triple <
              problem.encode.triples.length := by
          simpa [TypedProblem.encode] using indexLt
        have tripleLookup :=
          List.getElem?_idxOf tripleMember
        have getElemEq :
            problem.triples[problem.triples.idxOf triple] =
              triple := by
          rw [List.getElem?_eq_getElem indexLt] at tripleLookup
          exact Option.some.inj tripleLookup
        change
          (problem.triples.map problem.encodeTriple).getD
              (problem.triples.idxOf triple) default =
            problem.encodeTriple triple
        rw [List.getD_eq_getElem
          (l := problem.triples.map problem.encodeTriple)
          (d := default) encodedIndexLt]
        simp [getElemEq]
      simp only [PeriodicThreeDM.incidences,
        List.mem_filterMap]
      refine
        ⟨problem.triples.idxOf triple,
          ?_, ?_⟩
      · apply List.mem_range.mpr
        simpa [TypedProblem.encode] using indexLt
      · rw [encodedAt, referenceEncoded]
        have encodedAtomEq :
            (encodeReference elements
              (reference triple)).atom =
              elements.idxOf atom :=
          (encodeReference_atom_eq_iff elements
            (reference triple) ⟨atom, (0, 0)⟩
            (referencesListed triple tripleMember)
            atomMember).mpr atomEq
        rw [if_pos encodedAtomEq]
        rfl
    · simp at output

/-- The numbered and typed incidence lists differ only by the numbering map. -/
theorem encode_incidences_perm
    {Variable Element : Type*}
    [DecidableEq Variable] [DecidableEq Element]
    (problem : TypedProblem Variable)
    (elements : List Element)
    (reference : Triple Variable → Reference Element)
    (color : Gadget.WireColor)
    (referenceEncoded :
      ∀ triple,
        (problem.encodeTriple triple).reference color =
          encodeReference elements (reference triple))
    (referencesListed :
      ∀ triple ∈ problem.triples,
        (reference triple).atom ∈ elements)
    (triplesNodup : problem.triples.Nodup)
    (atom : Element) (atomMember : atom ∈ elements) :
    List.Perm
      (problem.encode.incidences color (elements.idxOf atom))
      ((referenceIncidences problem reference atom).map
        problem.encodeIncidence) := by
  apply List.Subperm.antisymm
  · apply
      (periodicThreeDM_incidences_nodup
        problem.encode color (elements.idxOf atom)).subperm
    intro incidence member
    exact
      (mem_encode_incidences_iff problem elements reference color
        referenceEncoded referencesListed triplesNodup atom
        atomMember incidence).mp member
  · have encodedNodup :=
      encodeIncidences_nodup problem
        (referenceIncidences problem reference atom)
        (referenceIncidences_nodup
          problem reference atom triplesNodup)
        (fun incidence member =>
          triple_mem_of_mem_referenceIncidences
            problem reference atom incidence member)
    apply encodedNodup.subperm
    intro incidence member
    exact
      (mem_encode_incidences_iff problem elements reference color
        referenceEncoded referencesListed triplesNodup atom
        atomMember incidence).mpr member

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
