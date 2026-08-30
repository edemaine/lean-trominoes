/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRoutes
import LeanTrominoes.PositionedPeriodicCNFRouteDirections

/-! # Prefix directions of retained representative routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open Gadget
open PeriodicOrthocrossing

/-- Anchor normalization of the first representative preserves the direction
word remaining after its old variable endpoint is deleted. -/
theorem representativeRoute_prefixDirections_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    unitSubdivisionDirections
        (representativeRoute source clauseIndex literalIndex).dropLast =
      unitSubdivisionDirections
        (rawRepresentativeRoute source clauseIndex literalIndex).dropLast := by
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
          clause ∈ normalizedClauses source :=
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
      exact
        PositionedPeriodicCNF.unitSubdivisionDirections_normalizeIncidenceRoute_dropLast
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
          gaugedClause
          (retainedDrawingPlanarSATLocalIncidenceRoutes source
            ((normalizedClauses source).idxOf clause) literalIndex)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
