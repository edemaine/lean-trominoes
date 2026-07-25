import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMCycleLinkIncidences
import LeanTrominoes.PeriodicOneInThreeToThreeDMMainClauseOccurrences
import Mathlib.Data.List.Perm.Subperm

/-!
# Source-occurrence correspondence for the planar periodic 3DM assembly

The assembled variable modules are ordered by occurring variable and used
slot, whereas source literals are ordered by clause and literal position.
Under the occurrence-three restriction, these two duplicate-free lists
contain exactly the same tagged occurrences.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Tagged occurrences in the exact variable/used-slot order of the
assembled modules. -/
def occurrenceEnumeration {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (TaggedOccurrence Variable) :=
  (occurrenceEntries source).filterMap fun entry =>
    occurrenceAt source entry.1 entry.2

/-- Every assembled occurrence came from the source tagged-literal list. -/
theorem tagged_mem_of_mem_occurrenceEnumeration
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (member : tagged ∈ occurrenceEnumeration source) :
    tagged ∈ PeriodicThreeSATThree.taggedLiterals source := by
  simp only [occurrenceEnumeration, List.mem_filterMap] at member
  rcases member with ⟨entry, entryMember, output⟩
  exact
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source entry.1 entry.2 tagged output).1

/-- Every tagged source occurrence has an assembled module when variables
occur at most three times. -/
theorem mem_occurrenceEnumeration_of_tagged_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    tagged ∈ occurrenceEnumeration source := by
  rcases
      PeriodicOneInThreeToThreeDM.exists_occurrenceSlot
        source occurrences tagged member with
    ⟨slot, lookup⟩
  simp only [occurrenceEnumeration, List.mem_filterMap]
  refine ⟨(tagged.1.atom, slot), ?_, lookup⟩
  rw [mem_occurrenceEntries_iff]
  exact
    ⟨PeriodicOneInThreeToThreeDM.atom_mem_occurringVariables_of_tagged_mem
        source tagged member,
      by
        simp only [usedSlots, List.mem_filter]
        refine ⟨?_, ?_⟩
        · cases slot <;>
            simp [allOccurrenceSlots,
              PeriodicOneInThreeToThreeDM.OccurrenceSlot.all]
        · exact Option.isSome_iff_exists.mpr ⟨tagged, lookup⟩⟩

/-- The assembled occurrence enumeration is duplicate-free. -/
theorem occurrenceEnumeration_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceEnumeration source).Nodup := by
  unfold occurrenceEnumeration
  apply List.Nodup.filterMap
  · intro firstEntry secondEntry tagged
      firstOutput secondOutput
    rcases firstEntry with ⟨firstAtom, firstSlot⟩
    rcases secondEntry with ⟨secondAtom, secondSlot⟩
    have firstAtomEq :=
      (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
        source firstAtom firstSlot tagged firstOutput).2
    have secondAtomEq :=
      (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
        source secondAtom secondSlot tagged secondOutput).2
    subst firstAtom
    subst secondAtom
    have slotEq :=
      PeriodicOneInThreeToThreeDM.occurrenceAt_slot_unique
        source tagged.1.atom tagged firstSlot secondSlot
          firstOutput secondOutput
    subst secondSlot
    rfl
  · exact occurrenceEntries_nodup source

/-- Module order and source order differ only by a permutation. -/
theorem occurrenceEnumeration_perm_taggedLiterals
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3) :
    List.Perm (occurrenceEnumeration source)
      (PeriodicThreeSATThree.taggedLiterals source) := by
  apply List.Subperm.antisymm
  · exact
      (occurrenceEnumeration_nodup source).subperm
        (tagged_mem_of_mem_occurrenceEnumeration source)
  · exact
      (PeriodicOneInThreeToThreeDM.taggedLiterals_nodup source).subperm
        (mem_occurrenceEnumeration_of_tagged_mem source occurrences)

/-- Literal position represented by one clause-terminal group. -/
def literalIndexOfTerminalGroup :
    PlanarThreeDM.X3CClauseTerminalGroup → Nat
  | .top => 0
  | .left => 1
  | .right => 2

@[simp]
theorem terminalGroupOfLiteralIndex_literalIndexOfTerminalGroup
    (group : PlanarThreeDM.X3CClauseTerminalGroup) :
    terminalGroupOfLiteralIndex
      (literalIndexOfTerminalGroup group) = group := by
  cases group <;> rfl

/-- Assembled occurrences attached to one selected clause terminal. -/
def terminalOccurrenceEnumeration {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (group : PlanarThreeDM.X3CClauseTerminalGroup) :
    List (TaggedOccurrence Variable) :=
  (occurrenceEnumeration source).filter fun tagged =>
    tagged.2.1 = clauseIndex ∧
      terminalGroupOfLiteralIndex tagged.2.2 = group

/-- The corresponding source-order tagged occurrences. -/
def sourceTerminalOccurrences {Variable : Type*}
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (group : PlanarThreeDM.X3CClauseTerminalGroup) :
    List (TaggedOccurrence Variable) :=
  (PeriodicThreeSATThree.taggedLiterals source).filter fun tagged =>
    tagged.2.1 = clauseIndex ∧
      terminalGroupOfLiteralIndex tagged.2.2 = group

/-- Assembled and source order enumerate the same occurrences at every
clause terminal. -/
theorem terminalOccurrenceEnumeration_perm_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (clauseIndex : Nat)
    (group : PlanarThreeDM.X3CClauseTerminalGroup) :
    List.Perm
      (terminalOccurrenceEnumeration source clauseIndex group)
      (sourceTerminalOccurrences source clauseIndex group) := by
  exact (occurrenceEnumeration_perm_taggedLiterals
    source occurrences).filter _

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
