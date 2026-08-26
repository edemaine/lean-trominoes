/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockIndex

/-! # Positioned clauses at implication-cycle block indices -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT
open OccurrenceSplitRing

/-- The semantic block origin plus a genuine local index selects exactly the
same positioned clause globally and inside that atom's Figure 7 block. -/
theorem exists_cycleClause_at_cycleBlockStart
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (atomMember : atom ∈ sourceVariables source.erase)
    (localClauseIndex : Nat)
    (localIndex :
      localClauseIndex <
        (PeriodicEightOccurrenceSplit.cycleClausesFor atom).length) :
    ∃ clause,
      (clause,
          cycleBlockStart (sourceVariables source.erase) atom +
            localClauseIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx ∧
      (clause, localClauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx := by
  have positionedLocalIndex :
      localClauseIndex <
        (cycleClausesFor sourcePlacement atom).length := by
    simpa [cycleClausesFor,
      OccurrenceSplitRing.cycleClausesFor_eq_cycleFormula] using localIndex
  rcases cycleClauseMetadata_blocks_lookup
      sourcePlacement (sourceVariables source.erase)
      atom atomMember localClauseIndex positionedLocalIndex with
    ⟨metadata, metadataLookup, metadataAtom, metadataIndex⟩
  have globalMetadataLookup :
      (allCycleClauseMetadata source sourcePlacement)[
          cycleBlockStart (sourceVariables source.erase) atom +
            localClauseIndex]? =
        some metadata := by
    simpa [allCycleClauseMetadata,
      cycleClauseMetadataBlocks] using metadataLookup
  have metadataMember :
      (metadata,
          cycleBlockStart (sourceVariables source.erase) atom +
            localClauseIndex) ∈
        (allCycleClauseMetadata source sourcePlacement).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr globalMetadataLookup
  have localMember :=
    allCycleClauseMetadata_valid
      source sourcePlacement
      (List.fst_mem_of_mem_zipIdx metadataMember)
  have globalClauseLookup :
      (allCycleClauses source sourcePlacement)[
          cycleBlockStart (sourceVariables source.erase) atom +
            localClauseIndex]? =
        some metadata.clause := by
    rw [← allCycleClauseMetadata_clauses source sourcePlacement,
      List.getElem?_map, globalMetadataLookup]
    rfl
  refine ⟨metadata.clause,
    List.mem_zipIdx_iff_getElem?.mpr globalClauseLookup, ?_⟩
  simpa [metadataAtom, metadataIndex] using localMember

/-- A tagged local Figure 7 template clause, after positioning and renaming
for `atom`, occurs at its semantic block-start/global index. -/
theorem positionedLocalCycleClause_mem_at_cycleBlockStart
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (atomMember : atom ∈ sourceVariables source.erase)
    {localClause : EmbeddedClause RingVertex}
    {localClauseIndex : Nat}
    (localClauseMember :
      (localClause, localClauseIndex) ∈ cycleFormula.zipIdx) :
    (positionedLocalCycleClause sourcePlacement atom localClause,
        cycleBlockStart (sourceVariables source.erase) atom +
          localClauseIndex) ∈
      (allCycleClauses source sourcePlacement).zipIdx := by
  have localIndex :
      localClauseIndex <
        (PeriodicEightOccurrenceSplit.cycleClausesFor atom).length := by
    simpa [OccurrenceSplitRing.cycleClausesFor_eq_cycleFormula] using
      List.snd_lt_of_mem_zipIdx localClauseMember
  rcases exists_cycleClause_at_cycleBlockStart
      source sourcePlacement atom atomMember
      localClauseIndex localIndex with
    ⟨clause, globalMember, localMember⟩
  have positionedLocalMember :
      (positionedLocalCycleClause sourcePlacement atom localClause,
          localClauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx := by
    rw [cycleClausesFor_eq_cycleFormula, List.zipIdx_map]
    exact List.mem_map.mpr ⟨(localClause, localClauseIndex),
      localClauseMember, rfl⟩
  have clauseEq :
      clause =
        positionedLocalCycleClause sourcePlacement atom localClause :=
    congrArg Prod.fst
      (PeriodicOrthocrossing.tagged_eq_of_mem_zipIdx_of_snd_eq
        localMember positionedLocalMember rfl)
  simpa [clauseEq] using globalMember

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
