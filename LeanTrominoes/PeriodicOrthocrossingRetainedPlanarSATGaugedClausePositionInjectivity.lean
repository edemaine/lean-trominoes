import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedClauseOrbits

/-!
# Injectivity of gauged retained clause positions

Equal positions in the anchor-normalized source determine equal literal
lists by the global clause-orbit classification.  Therefore selecting the
first representative of every literal list leaves a duplicate-free list of
stored clause positions.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

theorem anchorNormalized_clausePositionDeterminesLiterals
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
    ∀ first ∈
        (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses,
      ∀ second ∈
          (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).clauses,
        first.position = second.position →
          first.literals = second.literals := by
  rw [anchorNormalized_clauses_eq_metadata
    formula wellFormed degree isLocal clausesNonempty]
  intro first firstMember second secondMember positionEq
  rcases List.mem_map.mp firstMember with
    ⟨firstMetadata, firstMetadataMember, firstEq⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondMetadata, secondMetadataMember, secondEq⟩
  have firstValid :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula firstMetadataMember
  have secondValid :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula secondMetadataMember
  have firstNonempty :
      firstMetadata.clause.literals ≠ [] :=
    clausesNonempty firstMetadata.clause (by
      rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
      exact List.mem_map.mpr
        ⟨firstMetadata, firstMetadataMember, rfl⟩)
  have secondNonempty :
      secondMetadata.clause.literals ≠ [] :=
    clausesNonempty secondMetadata.clause (by
      rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
      exact List.mem_map.mpr
        ⟨secondMetadata, secondMetadataMember, rfl⟩)
  have residueEq :
      clauseResidue formula firstMetadata.clause =
        clauseResidue formula secondMetadata.clause := by
    calc
      clauseResidue formula firstMetadata.clause =
          first.position :=
        congrArg PositionedPeriodicClause.position firstEq
      _ = second.position := positionEq
      _ = clauseResidue formula secondMetadata.clause :=
        (congrArg PositionedPeriodicClause.position secondEq).symm
  have normalizedEq :=
    metadataGaugedNormalizedClause_eq_of_residue_eq
      wellFormed degree isLocal firstMetadata secondMetadata
      firstValid secondValid firstNonempty secondNonempty residueEq
  calc
    first.literals =
        metadataGaugedNormalizedClause formula firstMetadata :=
      (congrArg PositionedPeriodicClause.literals firstEq).symm
    _ = metadataGaugedNormalizedClause formula secondMetadata :=
      normalizedEq
    _ = second.literals :=
      congrArg PositionedPeriodicClause.literals secondEq

theorem deduplicated_storedClausePositions_nodup
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
    ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.map
      PositionedPeriodicClause.position).Nodup := by
  exact
    PositionedPeriodicCNF.deduplicateByLiterals_clausePositions_nodup
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (anchorNormalized_clausePositionDeterminesLiterals
        formula wellFormed degree isLocal clausesNonempty)

end LeanTrominoes.PeriodicOrthocrossing
