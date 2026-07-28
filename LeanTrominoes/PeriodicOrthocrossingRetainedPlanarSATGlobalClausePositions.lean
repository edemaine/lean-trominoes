import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATCarrierNoncarrierClausePositions

/-!
# Global injectivity of retained planar-SAT clause positions

The carrier/carrier, carrier/non-carrier, and non-carrier/non-carrier
geometric results combine to identify a retained component from any nonempty
clause position.  Local planarity then identifies the local clause index, and
the retained component-key enumeration identifies the global formula index.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Equal positions of nonempty retained clauses identify their geometric
component. -/
theorem retainedComponents_eq_of_clause_position_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (firstNonempty : first.clause.literals ≠ [])
    (secondNonempty : second.clause.literals ≠ [])
    (positionEq :
      first.clause.position = second.clause.position) :
    first.source.component = second.source.component := by
  by_cases firstCarrier :
      ∃ link, first.source.component = .carrier link
  · rcases firstCarrier with ⟨firstLink, firstCarrier⟩
    by_cases secondCarrier :
        ∃ link, second.source.component = .carrier link
    · rcases secondCarrier with ⟨secondLink, secondCarrier⟩
      exact
        retainedCarrierComponents_eq_of_clause_position_eq
          wellFormed degree isLocal first second
          firstValid secondValid firstLink secondLink
          firstCarrier secondCarrier positionEq
    · exact False.elim
        ((retainedCarrierClausePosition_ne_noncarrierClausePosition
          wellFormed degree isLocal first second
          firstValid secondValid firstLink firstCarrier
          secondCarrier secondNonempty) positionEq)
  · by_cases secondCarrier :
      ∃ link, second.source.component = .carrier link
    · rcases secondCarrier with ⟨secondLink, secondCarrier⟩
      exact False.elim
        ((retainedCarrierClausePosition_ne_noncarrierClausePosition
          wellFormed degree isLocal second first
          secondValid firstValid secondLink secondCarrier
          firstCarrier firstNonempty) positionEq.symm)
    · rcases
        first.source.component.exists_macrocellCenter_of_not_carrier
          formula firstCarrier with
        ⟨firstCenter, firstCenterEq⟩
      rcases
        second.source.component.exists_macrocellCenter_of_not_carrier
          formula secondCarrier with
        ⟨secondCenter, secondCenterEq⟩
      exact
        retainedNoncarrierComponents_eq_of_clause_position_eq
          wellFormed degree isLocal first second
          firstValid secondValid firstCenter secondCenter
          firstCenterEq secondCenterEq
          firstNonempty secondNonempty positionEq

/-- Equal positions of two globally indexed nonempty retained clauses identify
their global clause indices. -/
theorem retainedClauseIndex_eq_of_position_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (retainedDrawingPlanarSATFormula formula).zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (retainedDrawingPlanarSATFormula formula).zipIdx)
    (positionEq :
      firstClause.position = secondClause.position) :
    firstClauseIndex = secondClauseIndex := by
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula firstClauseMember with
    ⟨firstMetadata, firstLookup, firstClauseEq, firstValid⟩
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula secondClauseMember with
    ⟨secondMetadata, secondLookup, secondClauseEq, secondValid⟩
  have firstNonempty :
      firstMetadata.clause.literals ≠ [] := by
    rw [firstClauseEq]
    exact clausesNonempty firstClause
      (List.fst_mem_of_mem_zipIdx firstClauseMember)
  have secondNonempty :
      secondMetadata.clause.literals ≠ [] := by
    rw [secondClauseEq]
    exact clausesNonempty secondClause
      (List.fst_mem_of_mem_zipIdx secondClauseMember)
  have metadataPositionEq :
      firstMetadata.clause.position =
        secondMetadata.clause.position := by
    rw [firstClauseEq, secondClauseEq]
    exact positionEq
  have componentEq :=
    retainedComponents_eq_of_clause_position_eq
      wellFormed degree isLocal firstMetadata secondMetadata
      firstValid secondValid firstNonempty secondNonempty
      metadataPositionEq
  have localClauseIndexEq :=
    firstMetadata.localClauseIndex_eq_of_position_eq
      wellFormed degree isLocal secondMetadata
      firstValid secondValid componentEq metadataPositionEq
  exact
    retainedDrawingPlanarSAT_componentClauseKeysInjective
      formula firstLookup secondLookup
      componentEq localClauseIndexEq

/-- The assembled retained incidence drawing has globally injective clause
positions whenever all of its clauses are nonempty. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_clausePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).formula.map
      EmbeddedClause.position).Nodup := by
  rw [retainedDrawingPlanarSATLocalIncidenceDrawing_formula]
  rw [← retainedDrawingPlanarSATClauseMetadata_clauses,
    List.map_map]
  have keysNodup :=
    retainedDrawingPlanarSATClauseMetadata_componentClauseKeys_nodup
      formula
  have metadataNodup :
      (retainedDrawingPlanarSATClauseMetadata formula).Nodup :=
    keysNodup.of_map
      DrawingPlanarSATClauseMetadata.componentClauseKey
  apply metadataNodup.map_on
  intro first firstMem second secondMem positionEq
  have firstValid :=
    retainedDrawingPlanarSATClauseMetadata_valid formula firstMem
  have secondValid :=
    retainedDrawingPlanarSATClauseMetadata_valid formula secondMem
  have firstNonempty :
      first.clause.literals ≠ [] :=
    clausesNonempty first.clause
      (by
        rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
        exact List.mem_map.mpr ⟨first, firstMem, rfl⟩)
  have secondNonempty :
      second.clause.literals ≠ [] :=
    clausesNonempty second.clause
      (by
        rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
        exact List.mem_map.mpr ⟨second, secondMem, rfl⟩)
  have componentEq :=
    retainedComponents_eq_of_clause_position_eq
      wellFormed degree isLocal first second
      firstValid secondValid firstNonempty secondNonempty
      positionEq
  have localClauseIndexEq :=
    first.localClauseIndex_eq_of_position_eq
      wellFormed degree isLocal second
      firstValid secondValid componentEq positionEq
  apply List.inj_on_of_nodup_map keysNodup
    firstMem secondMem
  exact Prod.ext componentEq localClauseIndexEq

end LeanTrominoes.PeriodicOrthocrossing
