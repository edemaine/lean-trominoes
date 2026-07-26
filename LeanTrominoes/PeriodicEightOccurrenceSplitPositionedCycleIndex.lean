import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCycleDrawing

/-!
# Indexing the positioned occurrence-splitting cycles

The positioned fixed-eight formula stores all implication rings in one
`flatMap`.  A global route family must recover both the source atom and the
local Figure 7 clause index from a clause's position in that flattened list.

This module keeps that indexing information in a parallel metadata list and
proves that projecting its clauses gives exactly the existing flattened
formula.  Thus later route definitions can use list lookup directly, without
reconstructing the fixed block size arithmetically.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

/-- The data needed to select a certified route for one positioned cycle
clause. -/
structure CycleClauseMetadata
    (Variable : Type*) where
  clause :
    PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable)
  atom : Variable
  localClauseIndex : Nat

/-- Index every implication clause in one atom's local cycle block. -/
def cycleClauseMetadataFor
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    List (CycleClauseMetadata Variable) :=
  (cycleClausesFor sourcePlacement atom).zipIdx.map
    fun taggedClause =>
      ⟨taggedClause.1, atom, taggedClause.2⟩

/-- Metadata parallel to the flattened list of every positioned cycle
clause. -/
def allCycleClauseMetadata
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    List (CycleClauseMetadata Variable) :=
  (PeriodicThreeSATThree.sourceVariables source.erase).flatMap
    (cycleClauseMetadataFor sourcePlacement)

@[simp]
theorem cycleClauseMetadataFor_clauses
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (cycleClauseMetadataFor sourcePlacement atom).map
        CycleClauseMetadata.clause =
      cycleClausesFor sourcePlacement atom := by
  simp [cycleClauseMetadataFor, List.map_map,
    Function.comp_def]

/-- Forgetting the indexing metadata recovers the existing positioned cycle
list definitionally block-for-block. -/
@[simp]
theorem allCycleClauseMetadata_clauses
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    (allCycleClauseMetadata source sourcePlacement).map
        CycleClauseMetadata.clause =
      allCycleClauses source sourcePlacement := by
  simp [allCycleClauseMetadata, allCycleClauses,
    List.map_flatMap]

/-- Looking up a genuine flattened cycle clause yields metadata carrying
that exact clause. -/
theorem allCycleClauseMetadata_lookup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx) :
    ∃ metadata,
      (allCycleClauseMetadata
          source sourcePlacement)[cycleIndex]? =
        some metadata ∧
      metadata.clause = clause := by
  have clauseLookup :
      (allCycleClauses
          source sourcePlacement)[cycleIndex]? =
        some clause :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have projectedLookup :
      ((allCycleClauseMetadata source sourcePlacement).map
          CycleClauseMetadata.clause)[cycleIndex]? =
        some clause := by
    simpa using clauseLookup
  rw [List.getElem?_map] at projectedLookup
  simp only [Option.map_eq_some_iff] at projectedLookup
  exact projectedLookup

/-- Route lookup for the flattened cycle suffix, indexed relative to the
start of that suffix. -/
def allCycleRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun cycleIndex literalIndex =>
    match
      (allCycleClauseMetadata
        source sourcePlacement)[cycleIndex]?
    with
    | none => []
    | some metadata =>
        positionedCycleRoutes sourcePlacement
          metadata.atom metadata.localClauseIndex literalIndex

/-- A genuine flattened cycle clause selects the certified route family
recorded by its metadata. -/
theorem allCycleRoutes_of_clause_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    (literalIndex : Nat) :
    ∃ metadata : CycleClauseMetadata Variable,
      metadata.clause = clause ∧
      allCycleRoutes source sourcePlacement
          cycleIndex literalIndex =
        positionedCycleRoutes sourcePlacement
          metadata.atom metadata.localClauseIndex
          literalIndex := by
  rcases allCycleClauseMetadata_lookup
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  refine ⟨metadata, clauseEqual, ?_⟩
  simp [allCycleRoutes, metadataLookup]

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
