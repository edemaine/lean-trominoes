import LeanTrominoes.PeriodicOneInThreeToThreeDMBlueComplementUnique
import Mathlib.Data.List.Perm.Subperm

/-!
# Main clause occurrence enumeration

Main clause-blue incidences are enumerated by variable and occurrence slot,
whereas source clauses enumerate their literals syntactically.  Under the
occurrence-three bound, these presentations contain exactly the same tagged
occurrences, without duplication, and hence differ only by a permutation.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- The tagged occurrence contributed by one variable/slot pair to a selected
clause, if any. -/
def mainClauseOccurrenceOption {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (entry : Variable × OccurrenceSlot) :
    Option (TaggedOccurrence Variable) :=
  match occurrenceAt source entry.1 entry.2 with
  | none => none
  | some tagged =>
      if tagged.2.1 = clauseIndex then some tagged else none

/-- Main clause occurrences in the variable/slot order used by the typed 3DM
triple enumeration. -/
def mainClauseOccurrenceEnumeration {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) : List (TaggedOccurrence Variable) :=
  ((occurringVariables source) ×ˢ OccurrenceSlot.all).filterMap
    (mainClauseOccurrenceOption source clauseIndex)

/-- Membership in the variable/slot enumeration implies genuine tagged-list
membership and the selected clause index. -/
theorem mem_tagged_and_clause_of_mem_mainClauseOccurrenceEnumeration
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈
        mainClauseOccurrenceEnumeration source clauseIndex) :
    tagged ∈ PeriodicThreeSATThree.taggedLiterals source ∧
      tagged.2.1 = clauseIndex := by
  simp only [mainClauseOccurrenceEnumeration,
    List.mem_filterMap] at member
  rcases member with ⟨entry, entryMember, output⟩
  unfold mainClauseOccurrenceOption at output
  cases lookup : occurrenceAt source entry.1 entry.2 with
  | none => simp [lookup] at output
  | some current =>
      by_cases sameClause : current.2.1 = clauseIndex
      · simp [lookup, sameClause] at output
        subst current
        exact
          ⟨(occurrenceAt_mem_and_atom source entry.1 entry.2
              tagged lookup).1,
            sameClause⟩
      · simp [lookup, sameClause] at output

/-- Every source occurrence in the selected clause appears in the
variable/slot enumeration under the occurrence-three bound. -/
theorem mem_mainClauseOccurrenceEnumeration_of_tagged_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (clauseIndex : Nat) (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source)
    (sameClause : tagged.2.1 = clauseIndex) :
    tagged ∈ mainClauseOccurrenceEnumeration source clauseIndex := by
  rcases exists_occurrenceSlot source occurrences tagged member with
    ⟨slot, lookup⟩
  simp only [mainClauseOccurrenceEnumeration,
    List.mem_filterMap]
  refine
    ⟨(tagged.1.atom, slot),
      List.mem_product.mpr
        ⟨atom_mem_occurringVariables_of_tagged_mem
            source tagged member,
          ?_⟩,
      ?_⟩
  · cases slot <;> simp [OccurrenceSlot.all]
  · simp [mainClauseOccurrenceOption, lookup, sameClause]

/-- The variable/slot occurrence enumeration contains no duplicates. -/
theorem mainClauseOccurrenceEnumeration_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    (mainClauseOccurrenceEnumeration source clauseIndex).Nodup := by
  unfold mainClauseOccurrenceEnumeration
  apply List.Nodup.filterMap
  · intro firstEntry secondEntry tagged
      firstOutput secondOutput
    rcases firstEntry with ⟨firstAtom, firstSlot⟩
    rcases secondEntry with ⟨secondAtom, secondSlot⟩
    unfold mainClauseOccurrenceOption at firstOutput secondOutput
    cases firstLookup :
        occurrenceAt source firstAtom firstSlot with
    | none => simp [firstLookup] at firstOutput
    | some firstTagged =>
        cases secondLookup :
            occurrenceAt source secondAtom secondSlot with
        | none => simp [secondLookup] at secondOutput
        | some secondTagged =>
            by_cases firstClause :
                firstTagged.2.1 = clauseIndex
            · by_cases secondClause :
                  secondTagged.2.1 = clauseIndex
              · simp [firstLookup, firstClause] at firstOutput
                simp [secondLookup, secondClause] at secondOutput
                subst firstTagged
                subst secondTagged
                have firstAtomEq :=
                  (occurrenceAt_mem_and_atom source firstAtom
                    firstSlot tagged firstLookup).2
                have secondAtomEq :=
                  (occurrenceAt_mem_and_atom source secondAtom
                    secondSlot tagged secondLookup).2
                subst firstAtom
                subst secondAtom
                have slotEq :=
                  occurrenceAt_slot_unique source tagged.1.atom tagged
                    firstSlot secondSlot firstLookup secondLookup
                subst secondSlot
                rfl
              · simp [secondLookup, secondClause] at secondOutput
            · simp [firstLookup, firstClause] at firstOutput
  · exact
      (occurringVariables_nodup source).product
        (by decide)

/-- The source-order occurrence list of one clause is duplicate-free. -/
theorem clauseOccurrences_nodup {Variable : Type*}
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    (clauseOccurrences source clauseIndex).Nodup := by
  exact (taggedLiterals_nodup source).filter _

/-- Under the occurrence-three bound, variable/slot order and source clause
order enumerate the same occurrences up to permutation. -/
theorem mainClauseOccurrenceEnumeration_perm_clauseOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (clauseIndex : Nat) :
    List.Perm
      (mainClauseOccurrenceEnumeration source clauseIndex)
      (clauseOccurrences source clauseIndex) := by
  apply List.Subperm.antisymm
  · apply
      (mainClauseOccurrenceEnumeration_nodup
        source clauseIndex).subperm
    intro tagged member
    rw [clauseOccurrences]
    have data :=
      mem_tagged_and_clause_of_mem_mainClauseOccurrenceEnumeration
        source clauseIndex tagged member
    exact List.mem_filter.mpr ⟨data.1, by simpa using data.2⟩
  · apply (clauseOccurrences_nodup source clauseIndex).subperm
    intro tagged member
    rw [clauseOccurrences] at member
    rcases List.mem_filter.mp member with
      ⟨taggedMember, sameClause⟩
    exact
      mem_mainClauseOccurrenceEnumeration_of_tagged_mem
        source occurrences clauseIndex tagged taggedMember
          (by simpa using sameClause)

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
