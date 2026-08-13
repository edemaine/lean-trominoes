/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMMainClauseOccurrences

/-!
# Source-clause values from tagged occurrences

Filtering the global tagged-literal list at a valid clause index recovers that
source clause's indexed literals up to permutation.  Mapping either list to
literal truth values therefore preserves the exact-one predicate.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- One source clause tagged with a fixed clause index and its literal
indices. -/
def taggedClauseOccurrences {Variable : Type*}
    (clauseIndex : Nat) (clause : PeriodicClause Variable) :
    List (TaggedOccurrence Variable) :=
  clause.zipIdx.map fun tagged =>
    (tagged.1, clauseIndex, tagged.2)

/-- The explicitly tagged occurrence list of one clause has no duplicates
because its literal indices are unique. -/
theorem taggedClauseOccurrences_nodup {Variable : Type*}
    (clauseIndex : Nat) (clause : PeriodicClause Variable) :
    (taggedClauseOccurrences clauseIndex clause).Nodup := by
  apply List.Nodup.of_map fun tagged => tagged.2.2
  simpa [taggedClauseOccurrences, List.map_map,
    Function.comp_def] using
      List.nodup_zipIdx_map_snd clause

/-- A valid source clause lookup makes the filtered global occurrence list
and the explicitly indexed clause list extensionally equal as sets. -/
theorem mem_clauseOccurrences_iff_mem_taggedClauseOccurrences
    {Variable : Type*} (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (tagged : TaggedOccurrence Variable) :
    tagged ∈ clauseOccurrences source clauseIndex ↔
      tagged ∈ taggedClauseOccurrences clauseIndex clause := by
  constructor
  · intro member
    unfold clauseOccurrences at member
    rcases List.mem_filter.mp member with
      ⟨taggedMember, sameClause⟩
    have sameClauseEq : tagged.2.1 = clauseIndex := by
      simpa using sameClause
    have literalLookup :=
      literalAt_eq_some_of_tagged_mem source tagged taggedMember
    rw [sameClauseEq, literalAt, clauseLookup] at literalLookup
    unfold taggedClauseOccurrences
    apply List.mem_map.mpr
    refine
      ⟨(tagged.1, tagged.2.2),
        (List.mem_zipIdx_iff_getElem?).mpr ?_,
        ?_⟩
    · simpa using literalLookup
    · rcases tagged with
        ⟨literal, taggedClauseIndex, taggedLiteralIndex⟩
      simp only at sameClauseEq
      subst taggedClauseIndex
      rfl
  · intro member
    unfold taggedClauseOccurrences at member
    rcases List.mem_map.mp member with
      ⟨indexedLiteral, indexedMember, taggedEq⟩
    have clauseMember :
        (clause, clauseIndex) ∈ source.clauses.zipIdx :=
      (List.mem_zipIdx_iff_getElem?).mpr clauseLookup
    unfold clauseOccurrences
    apply List.mem_filter.mpr
    constructor
    · unfold PeriodicThreeSATThree.taggedLiterals
      apply List.mem_flatMap.mpr
      refine
        ⟨(clause, clauseIndex), clauseMember,
          List.mem_map.mpr
            ⟨indexedLiteral, indexedMember, taggedEq⟩⟩
    · subst tagged
      simp

/-- At a valid source clause index, filtered global order and source literal
order differ only by a permutation. -/
theorem clauseOccurrences_perm_taggedClauseOccurrences
    {Variable : Type*} (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    List.Perm (clauseOccurrences source clauseIndex)
      (taggedClauseOccurrences clauseIndex clause) := by
  apply List.Subperm.antisymm
  · apply (clauseOccurrences_nodup source clauseIndex).subperm
    intro tagged member
    exact
      (mem_clauseOccurrences_iff_mem_taggedClauseOccurrences
        source clauseIndex clause clauseLookup tagged).mp member
  · apply
      (taggedClauseOccurrences_nodup
        clauseIndex clause).subperm
    intro tagged member
    exact
      (mem_clauseOccurrences_iff_mem_taggedClauseOccurrences
        source clauseIndex clause clauseLookup tagged).mpr member

/-- Forgetting indices from the filtered occurrence list recovers the source
clause up to permutation. -/
theorem clauseOccurrences_literals_perm {Variable : Type*}
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    List.Perm
      ((clauseOccurrences source clauseIndex).map fun tagged =>
        tagged.1)
      clause := by
  have occurrencePerm :=
    (clauseOccurrences_perm_taggedClauseOccurrences
      source clauseIndex clause clauseLookup).map
        (fun tagged => tagged.1)
  simpa [taggedClauseOccurrences, List.map_map,
    Function.comp_def] using occurrencePerm

/-- Literal truth values obtained from filtered tagged occurrences are a
permutation of the ordinary source clause values. -/
theorem clauseOccurrences_values_perm_clauseValues
    {Variable : Type*} (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    List.Perm
      ((clauseOccurrences source clauseIndex).map fun tagged =>
        PeriodicOneInThree.literalTruth
          assignment translate tagged.1)
      (PeriodicOneInThree.clauseValues
        assignment translate clause) := by
  change
    List.Perm
      ((clauseOccurrences source clauseIndex).map fun tagged =>
        PeriodicOneInThree.literalTruth
          assignment translate tagged.1)
      (clause.map fun literal =>
        PeriodicOneInThree.literalTruth
          assignment translate literal)
  have valuesPerm :=
    (clauseOccurrences_literals_perm
      source clauseIndex clause clauseLookup).map
        (PeriodicOneInThree.literalTruth assignment translate)
  simpa [List.map_map, Function.comp_def] using valuesPerm

/-- Exact-one is invariant under permutation of its Boolean inputs. -/
theorem exactlyOne_iff_of_perm {first second : List Bool}
    (permutation : List.Perm first second) :
    PeriodicOneInThree.ExactlyOne first ↔
      PeriodicOneInThree.ExactlyOne second := by
  unfold PeriodicOneInThree.ExactlyOne
  rw [List.perm_iff_count.mp permutation true]

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
