/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutes
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRoutes

/-! # Lengths of final retained representative routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Anchor normalization of the first representative preserves its listed
route length. -/
theorem representativeRoute_length_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    (representativeRoute source clauseIndex literalIndex).length =
      (rawRepresentativeRoute source clauseIndex literalIndex).length := by
  unfold representativeRoute rawRepresentativeRoute
  generalize clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? = clauseOption
  cases clauseOption with
  | none => rfl
  | some clause =>
      have clauseMember : clause ∈ deduplicatedClauses source :=
        List.mem_iff_getElem?.mpr ⟨clauseIndex, clauseLookup⟩
      have normalizedMember : clause ∈ normalizedClauses source :=
        List.mem_dedup.mp clauseMember
      have representativeLt :
          (normalizedClauses source).idxOf clause <
            (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              source).clauses.length := by
        rw [gaugedPositionedSource_clauses_length_eq]
        exact List.idxOf_lt_length_iff.mpr normalizedMember
      let gaugedClause :=
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).clauses[(normalizedClauses source).idxOf clause]
      have gaugedClauseLookup :
          (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            source).clauses[(normalizedClauses source).idxOf clause]? =
            some gaugedClause :=
        List.getElem?_eq_getElem representativeLt
      unfold
        retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
      simp only
      rw [gaugedClauseLookup]
      simp [PositionedPeriodicCNF.normalizeIncidenceRoute]

/-- Final clause deduplication and outer anchor normalization preserve the
listed route length of the raw metadata representative. -/
theorem incidenceRoutes_length_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    (FormulaShapeRetainedPlanarDirection.incidenceRoutes
        source clauseIndex literalIndex).length =
      (rawRepresentativeRoute source clauseIndex literalIndex).length := by
  let normalizedSource :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source
  let normalizedRoutes :=
    retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source
  change
    (normalizedSource.deduplicatedIncidenceRoutes
      placement normalizedRoutes clauseIndex literalIndex).length = _
  unfold PositionedPeriodicCNF.deduplicatedIncidenceRoutes
  generalize clauseLookup :
      normalizedSource.deduplicateByLiterals.clauses[clauseIndex]? =
        clauseOption
  cases clauseOption with
  | none =>
      have metadataLookup :
          (deduplicatedClauses source)[clauseIndex]? = none := by
        have lookup := positionedSource_clauseLiterals?_eq source clauseIndex
        change
          (normalizedSource.deduplicateByLiterals.clauses[clauseIndex]?).map
              PositionedPeriodicClause.literals = _
          at lookup
        rw [clauseLookup] at lookup
        exact lookup.symm
      simp [rawRepresentativeRoute, metadataLookup]
  | some clause =>
      have metadataLookup :
          (deduplicatedClauses source)[clauseIndex]? =
            some clause.literals := by
        have lookup := positionedSource_clauseLiterals?_eq source clauseIndex
        change
          (normalizedSource.deduplicateByLiterals.clauses[clauseIndex]?).map
              PositionedPeriodicClause.literals = _
          at lookup
        rw [clauseLookup] at lookup
        exact lookup.symm
      rw [show
        (PositionedPeriodicCNF.normalizeIncidenceRoute
          placement clause
          (normalizedRoutes
            (normalizedSource.representativeClauseIndex clause.literals)
            literalIndex)).length =
          (normalizedRoutes
            (normalizedSource.representativeClauseIndex clause.literals)
            literalIndex).length by
        simp [PositionedPeriodicCNF.normalizeIncidenceRoute]]
      rw [representativeClauseIndex_eq source clause.literals]
      calc
        (normalizedRoutes
            ((normalizedClauses source).idxOf clause.literals)
            literalIndex).length =
            (representativeRoute
              source clauseIndex literalIndex).length := by
          unfold representativeRoute
          rw [metadataLookup]
        _ = _ := representativeRoute_length_eq_rawRepresentativeRoute
          source clauseIndex literalIndex

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
