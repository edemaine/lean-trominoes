/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutes
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRouteData

/-! # Representative retained first directions from raw metadata routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The gauged positioned retained source and its normalized metadata clause
list have the same length. -/
theorem gaugedPositionedSource_clauses_length_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source).clauses.length =
      (normalizedClauses source).length := by
  have lengthEq := congrArg List.length
    (anchorNormalized_erase_clauses_eq source)
  simpa [
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.anchorNormalize,
    PositionedPeriodicCNF.erase] using lengthEq

/-- The first normalized representative route and its underlying raw local
metadata route have the same first direction. -/
theorem representativeRoute_firstDirection_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        (representativeRoute source clauseIndex literalIndex) =
      AxisDirection.polylineFirstDirection
        (rawRepresentativeRoute source clauseIndex literalIndex) := by
  unfold representativeRoute rawRepresentativeRoute
  generalize clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? = clauseOption
  cases clauseOption with
  | none => rfl
  | some clause =>
      have clauseMember :
          clause ∈ deduplicatedClauses source :=
        List.mem_iff_getElem?.mpr ⟨clauseIndex, clauseLookup⟩
      have normalizedMember :
          clause ∈ normalizedClauses source := by
        exact List.mem_dedup.mp clauseMember
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
      exact
        PositionedPeriodicCNF.polylineFirstDirection_normalizeIncidenceRoute
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
          gaugedClause
          (retainedDrawingPlanarSATLocalIncidenceRoutes source
            ((normalizedClauses source).idxOf clause) literalIndex)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
