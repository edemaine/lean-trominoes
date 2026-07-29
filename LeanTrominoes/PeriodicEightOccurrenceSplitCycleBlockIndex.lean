import LeanTrominoes.PeriodicEightOccurrenceSplitCycleOccurrenceIndex
import LeanTrominoes.PeriodicEightOccurrenceSplitRouteTerminalDirections

/-!
# Global implication-cycle block indices

The semantic fixed-eight formula flattens one constant Figure 7 implication
ring for every source atom.  This file connects a filtered occurrence in that
global suffix to the atom's local ring indices and to the corresponding
positioned route lookup.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree
open PlanarThreeSAT

/-- Shift only the clause index of a tagged occurrence. -/
def shiftTaggedOccurrence
    {Variable : Type*}
    (shift : Nat)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable) :
    PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable :=
  (tagged.1, shift + tagged.2.1, tagged.2.2)

/-- Changing the initial clause index translates every flattened tag by the
same amount. -/
theorem taggedLiteralsFrom_add
    {Variable : Type*}
    (clauses : List (PeriodicClause Variable))
    (start shift : Nat) :
    taggedLiteralsFrom (shift + start) clauses =
      (taggedLiteralsFrom start clauses).map
        (shiftTaggedOccurrence shift) := by
  induction clauses generalizing start with
  | nil =>
      rfl
  | cons clause rest induction =>
      rw [show clause :: rest = [clause] ++ rest by rfl,
        taggedLiteralsFrom_append,
        taggedLiteralsFrom_append,
        List.map_append]
      congr 1
      · simp [taggedLiteralsFrom,
          shiftTaggedOccurrence]
      · simpa [Nat.add_assoc] using
          induction (start + 1)

/-- Clause/literal indices of one semantic ring tagged at an arbitrary
global starting clause index. -/
def shiftedCycleOccurrenceIndicesFor
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (atom : Variable)
    (output : ThreeOccurrenceVariable Variable) :
    List (Nat × Nat) :=
  (taggedLiteralsFrom start (cycleClausesFor atom))
    |>.filter (fun tagged => tagged.1.atom = output)
    |>.map fun tagged => (tagged.2.1, tagged.2.2)

/-- Shifting a semantic ring's clause origin adds the same amount to every
filtered local clause index. -/
theorem shiftedCycleOccurrenceIndicesFor_eq_map
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (atom : Variable)
    (output : ThreeOccurrenceVariable Variable) :
    shiftedCycleOccurrenceIndicesFor start atom output =
      (cycleOccurrenceIndicesFor atom output).map
        fun index => (start + index.1, index.2) := by
  unfold shiftedCycleOccurrenceIndicesFor
    cycleOccurrenceIndicesFor
  have shifted :=
    taggedLiteralsFrom_add
      (cycleClausesFor atom) 0 start
  simp only [Nat.add_zero] at shifted
  rw [shifted]
  generalize
    taggedLiteralsFrom 0 (cycleClausesFor atom) =
      tagged
  induction tagged with
  | nil =>
      rfl
  | cons head rest induction =>
      by_cases same : head.1.atom = output
      · simp [same, induction,
          shiftTaggedOccurrence]
      · simp [same, induction,
          shiftTaggedOccurrence]

/-- Every zero-based tag names a clause inside the tagged list. -/
theorem clauseIndex_lt_of_mem_taggedLiteralsFrom_zero
    {Variable : Type*}
    (clauses : List (PeriodicClause Variable))
    {tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable}
    (taggedMember :
      tagged ∈ taggedLiteralsFrom 0 clauses) :
    tagged.2.1 < clauses.length := by
  unfold taggedLiteralsFrom at taggedMember
  rcases List.mem_flatMap.mp taggedMember with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteralMember⟩
  rcases List.mem_map.mp taggedLiteralMember with
    ⟨taggedLiteral, _taggedLiteralMember,
      taggedEqual⟩
  subst tagged
  exact (List.mem_zipIdx' taggedClauseMember).1

/-- Every filtered local cycle index names a genuine clause of that
semantic ring. -/
theorem cycleOccurrenceIndicesFor_clauseIndex_lt
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable)
    (output : ThreeOccurrenceVariable Variable)
    {index : Nat × Nat}
    (indexMember :
      index ∈ cycleOccurrenceIndicesFor atom output) :
    index.1 < (cycleClausesFor atom).length := by
  unfold cycleOccurrenceIndicesFor at indexMember
  rcases List.mem_map.mp indexMember with
    ⟨tagged, taggedMember, indexEqual⟩
  have taggedSourceMember :=
    (List.mem_filter.mp taggedMember).1
  have clauseIndexLt :=
    clauseIndex_lt_of_mem_taggedLiteralsFrom_zero
      (cycleClausesFor atom) taggedSourceMember
  simpa [← indexEqual] using clauseIndexLt

/-- A ring generated for another source atom contributes no occurrence of
the requested copy. -/
theorem cycleOccurrenceIndicesFor_ringCopy_eq_nil_of_ne
    {Variable : Type*} [DecidableEq Variable]
    {first second : Variable}
    (different : first ≠ second)
    (vertex : RingVertex) :
    cycleOccurrenceIndicesFor first
        (ringCopy second vertex) = [] := by
  unfold cycleOccurrenceIndicesFor
  rw [taggedLiteralsFrom_cycleClausesFor]
  generalize
    embeddedCNFIncidences cycleFormula = incidences
  induction incidences with
  | nil =>
      rfl
  | cons incidence rest induction =>
      have renamedDifferent :
          ringCopy first incidence.literal.1 ≠
            ringCopy second vertex := by
        intro equal
        apply different
        have firstCoordinate :
            (ringCopy first incidence.literal.1).1 =
              first := by
          cases incidence.literal.1 <;> rfl
        have secondCoordinate :
            (ringCopy second vertex).1 =
              second := by
          cases vertex <;> rfl
        exact firstCoordinate.symm.trans
          ((congrArg
            (fun occurrence :
              ThreeOccurrenceVariable Variable =>
                occurrence.1)
            equal).trans secondCoordinate)
      simp [renamedDifferent, induction,
        periodicCycleOccurrence]

/-- Number of cycle clauses preceding the first block of `atom` in an
explicit atom list. -/
def cycleBlockStart
    {Variable : Type*} [DecidableEq Variable] :
    List Variable → Variable → Nat
  | [], _ => 0
  | head :: rest, atom =>
      if head = atom then 0
      else
        (cycleClausesFor head).length +
          cycleBlockStart rest atom

/-- Global clause/literal indices of one output variable among the
flattened implication rings generated for an explicit atom list. -/
def cycleOccurrenceIndicesFrom
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (atoms : List Variable)
    (output : ThreeOccurrenceVariable Variable) :
    List (Nat × Nat) :=
  (taggedLiteralsFrom start (cyclesFor atoms))
    |>.filter (fun tagged => tagged.1.atom = output)
    |>.map fun tagged => (tagged.2.1, tagged.2.2)

/-- The flattened occurrence-index list decomposes block-for-block. -/
theorem cycleOccurrenceIndicesFrom_cons
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (head : Variable)
    (rest : List Variable)
    (output : ThreeOccurrenceVariable Variable) :
    cycleOccurrenceIndicesFrom start
        (head :: rest) output =
      shiftedCycleOccurrenceIndicesFor
          start head output ++
        cycleOccurrenceIndicesFrom
          (start + (cycleClausesFor head).length)
          rest output := by
  unfold cycleOccurrenceIndicesFrom
    shiftedCycleOccurrenceIndicesFor
  rw [show cyclesFor (head :: rest) =
      cycleClausesFor head ++ cyclesFor rest by rfl,
    taggedLiteralsFrom_append,
    List.filter_append, List.map_append]

/-- If an atom is absent from the block list, none of those rings can
contribute one of its copies. -/
theorem cycleOccurrenceIndicesFrom_ringCopy_eq_nil_of_not_mem
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (atoms : List Variable)
    (atom : Variable) (vertex : RingVertex)
    (atomAbsent : atom ∉ atoms) :
    cycleOccurrenceIndicesFrom start atoms
        (ringCopy atom vertex) = [] := by
  induction atoms generalizing start with
  | nil =>
      rfl
  | cons head rest induction =>
      have headDifferent : head ≠ atom := by
        intro same
        exact atomAbsent
          (by simp [same])
      have tailAbsent : atom ∉ rest := by
        intro member
        exact atomAbsent
          (List.mem_cons_of_mem head member)
      rw [cycleOccurrenceIndicesFrom_cons,
        shiftedCycleOccurrenceIndicesFor_eq_map,
        cycleOccurrenceIndicesFor_ringCopy_eq_nil_of_ne
          headDifferent vertex,
        induction
          (start +
            (cycleClausesFor head).length)
          tailAbsent]
      rfl

/-- In a duplicate-free block list containing `atom`, filtering its copy
recovers the local ring indices in the same order, shifted by the unique
block's global origin. -/
theorem cycleOccurrenceIndicesFrom_ringCopy
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (atoms : List Variable)
    (atom : Variable) (vertex : RingVertex)
    (atomsNodup : atoms.Nodup)
    (atomMember : atom ∈ atoms) :
    cycleOccurrenceIndicesFrom start atoms
        (ringCopy atom vertex) =
      (cycleOccurrenceIndicesFor atom
        (ringCopy atom vertex)).map
        fun index =>
          (start + cycleBlockStart atoms atom +
            index.1, index.2) := by
  induction atoms generalizing start with
  | nil =>
      simp at atomMember
  | cons head rest induction =>
      have headNodup := List.nodup_cons.mp atomsNodup
      by_cases same : head = atom
      · subst head
        rw [cycleOccurrenceIndicesFrom_cons,
          shiftedCycleOccurrenceIndicesFor_eq_map,
          cycleOccurrenceIndicesFrom_ringCopy_eq_nil_of_not_mem
            (start +
              (cycleClausesFor atom).length)
            rest atom vertex headNodup.1]
        simp [cycleBlockStart]
      · have tailMember : atom ∈ rest := by
          simpa [same, Ne.symm same] using atomMember
        rw [cycleOccurrenceIndicesFrom_cons,
          shiftedCycleOccurrenceIndicesFor_eq_map,
          cycleOccurrenceIndicesFor_ringCopy_eq_nil_of_ne
            same vertex,
          induction
            (start +
              (cycleClausesFor head).length)
            headNodup.2 tailMember]
        simp [cycleBlockStart, same,
          Nat.add_assoc]

/-- Projecting the shifted implication suffix to presentation indices is
definitionally the explicit-block construction above. -/
theorem cycleOccurrencesOf_indices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (output : ThreeOccurrenceVariable Variable) :
    (cycleOccurrencesOf source occurrencePorts output).map
        (fun tagged => (tagged.2.1, tagged.2.2)) =
      cycleOccurrenceIndicesFrom
        (occurrenceClauses source occurrencePorts).length
        (sourceVariables source) output := by
  unfold cycleOccurrencesOf cycleOccurrenceIndicesFrom
    allCycleClauses cyclesFor
  generalize
    taggedLiteralsFrom
      (occurrenceClauses source occurrencePorts).length
      (List.flatMap cycleClausesFor
        (sourceVariables source)) = tagged
  induction tagged with
  | nil =>
      rfl
  | cons head rest induction =>
      by_cases same : head.1.atom = output
      · simp [same, induction]
      · simp [same, induction]

/-- For a source atom, the two global cycle occurrences of one ring copy
are its local indices in the certified order, shifted past the copied prefix
and preceding atom blocks. -/
theorem cycleOccurrencesOf_ringCopy_indices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (atom : Variable) (vertex : RingVertex)
    (atomMember : atom ∈ sourceVariables source) :
    (cycleOccurrencesOf source occurrencePorts
        (ringCopy atom vertex)).map
        (fun tagged => (tagged.2.1, tagged.2.2)) =
      (cycleOccurrenceIndicesFor atom
        (ringCopy atom vertex)).map
        fun index =>
          ((occurrenceClauses
              source occurrencePorts).length +
              cycleBlockStart
                (sourceVariables source) atom +
              index.1,
            index.2) := by
  rw [cycleOccurrencesOf_indices]
  exact cycleOccurrenceIndicesFrom_ringCopy
    (occurrenceClauses source occurrencePorts).length
    (sourceVariables source) atom vertex
    (by
      unfold sourceVariables
      exact List.nodup_dedup _)
    atomMember

end PeriodicEightOccurrenceSplit

namespace PeriodicEightOccurrenceSplitPositioned

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Looking up a local clause index in one metadata block records exactly
that block's atom and index. -/
theorem cycleClauseMetadataFor_lookup_index
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (localClauseIndex : Nat)
    (localIndex :
      localClauseIndex <
        (cycleClausesFor
          sourcePlacement atom).length) :
    ∃ metadata : CycleClauseMetadata Variable,
      (cycleClauseMetadataFor
          sourcePlacement atom)[localClauseIndex]? =
        some metadata ∧
      metadata.atom = atom ∧
      metadata.localClauseIndex = localClauseIndex := by
  unfold cycleClauseMetadataFor
  rw [List.getElem?_map]
  simp [localIndex,
    List.getElem_zipIdx]

/-- Metadata blocks for an explicit atom list, before specializing to a
positioned source formula. -/
def cycleClauseMetadataBlocks
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atoms : List Variable) :
    List (CycleClauseMetadata Variable) :=
  atoms.flatMap
    (cycleClauseMetadataFor sourcePlacement)

/-- The recursive semantic block origin also selects the corresponding
local entry in the parallel positioned metadata list. -/
theorem cycleClauseMetadata_blocks_lookup
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atoms : List Variable) (atom : Variable)
    (atomMember : atom ∈ atoms)
    (localClauseIndex : Nat)
    (localIndex :
      localClauseIndex <
        (cycleClausesFor
          sourcePlacement atom).length) :
    ∃ metadata : CycleClauseMetadata Variable,
      (cycleClauseMetadataBlocks sourcePlacement atoms)[
        cycleBlockStart atoms atom + localClauseIndex]? =
        some metadata ∧
      metadata.atom = atom ∧
      metadata.localClauseIndex =
        localClauseIndex := by
  induction atoms with
  | nil =>
      simp at atomMember
  | cons head rest induction =>
      by_cases same : head = atom
      · subst head
        have localMetadata :=
          cycleClauseMetadataFor_lookup_index
            sourcePlacement atom localClauseIndex
            localIndex
        have localMetadataIndex :
            localClauseIndex <
              (cycleClauseMetadataFor
                sourcePlacement atom).length := by
          simpa [cycleClauseMetadataFor] using
            localIndex
        simp only [cycleBlockStart, ↓reduceIte,
          Nat.zero_add, cycleClauseMetadataBlocks,
          List.flatMap_cons]
        rw [List.getElem?_append_left
          localMetadataIndex]
        exact localMetadata
      · have tailMember : atom ∈ rest := by
          simpa [same, Ne.symm same] using atomMember
        have tailMetadata :=
          induction tailMember
        have headLength :
            (cycleClauseMetadataFor
              sourcePlacement head).length =
              (cycleClausesFor
                sourcePlacement head).length := by
          simp [cycleClauseMetadataFor]
        have positionedSemanticLength :
            (cycleClausesFor
                sourcePlacement head).length =
              (PeriodicEightOccurrenceSplit.cycleClausesFor
                head).length := by
          simp [PeriodicEightOccurrenceSplitPositioned.cycleClausesFor]
        have headSemanticLength :
            (cycleClauseMetadataFor
                sourcePlacement head).length =
              (PeriodicEightOccurrenceSplit.cycleClausesFor
                head).length :=
          headLength.trans positionedSemanticLength
        have headLengthLe :
            (cycleClauseMetadataFor
                sourcePlacement head).length ≤
              cycleBlockStart (head :: rest) atom +
                localClauseIndex := by
          rw [headSemanticLength]
          simp only [cycleBlockStart, if_neg same]
          omega
        simp only [cycleClauseMetadataBlocks,
          List.flatMap_cons]
        rw [List.getElem?_append_right headLengthLe]
        simpa [cycleBlockStart, same,
          headSemanticLength,
          cycleClauseMetadataBlocks,
          Nat.add_assoc] using tailMetadata

/-- The semantic block origin selects exactly the certified positioned
route family for that atom and local clause index. -/
theorem allCycleRoutes_cycleBlockStart
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (atomMember : atom ∈ sourceVariables source.erase)
    (localClauseIndex literalIndex : Nat)
    (localIndex :
      localClauseIndex <
        (PeriodicEightOccurrenceSplit.cycleClausesFor
          atom).length) :
    allCycleRoutes source sourcePlacement
        (cycleBlockStart
          (sourceVariables source.erase) atom +
          localClauseIndex)
        literalIndex =
      positionedCycleRoutes sourcePlacement atom
        localClauseIndex literalIndex := by
  have positionedLocalIndex :
      localClauseIndex <
        (cycleClausesFor
          sourcePlacement atom).length := by
    simpa [
      PeriodicEightOccurrenceSplitPositioned.cycleClausesFor,
      OccurrenceSplitRing.cycleClausesFor_eq_cycleFormula]
      using localIndex
  rcases cycleClauseMetadata_blocks_lookup
      sourcePlacement
      (sourceVariables source.erase) atom atomMember
      localClauseIndex positionedLocalIndex with
    ⟨metadata, metadataLookup,
      metadataAtom, metadataIndex⟩
  have globalMetadataLookup :
      (allCycleClauseMetadata
        source sourcePlacement)[
          cycleBlockStart
            (sourceVariables source.erase) atom +
            localClauseIndex]? =
        some metadata := by
    simpa [allCycleClauseMetadata,
      cycleClauseMetadataBlocks] using
        metadataLookup
  simp [allCycleRoutes, globalMetadataLookup,
    metadataAtom, metadataIndex]

/-- Hence a route selected by a semantic block/local index pair has exactly
the corresponding local Figure 7 terminal direction. -/
theorem allCycleRoutes_cycleBlockStart_lastDirection
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (atomMember : atom ∈ sourceVariables source.erase)
    (localClauseIndex literalIndex : Nat)
    (localIndex :
      localClauseIndex <
        (PeriodicEightOccurrenceSplit.cycleClausesFor
          atom).length) :
    AxisDirection.polylineLastDirection
        (allCycleRoutes source sourcePlacement
          (cycleBlockStart
            (sourceVariables source.erase) atom +
            localClauseIndex)
          literalIndex) =
      AxisDirection.polylineLastDirection
        (OccurrenceSplitRing.cycleRoutes
          localClauseIndex literalIndex) := by
  rw [allCycleRoutes_cycleBlockStart
    source sourcePlacement atom atomMember
    localClauseIndex literalIndex localIndex,
    positionedCycleRoutes_lastDirection]

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
