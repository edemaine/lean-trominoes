/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRoutes
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRoutes
import LeanTrominoes.PositionedPeriodicCNFDeduplicationTerminalPorts

/-! # Final terminal vectors from representative metadata routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- Final clause deduplication and anchor normalization preserve the complete
terminal vector of the first normalized metadata route representing the
retained clause. -/
theorem incidenceRoutes_routeTerminalVector_eq_representativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    routeTerminalVector
        (FormulaShapeRetainedPlanarDirection.incidenceRoutes
          source clauseIndex literalIndex) =
      routeTerminalVector
        (representativeRoute source clauseIndex literalIndex) := by
  let normalizedSource :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source
  let normalizedRoutes :=
    retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source
  change routeTerminalVector
      (normalizedSource.deduplicatedIncidenceRoutes
        placement normalizedRoutes clauseIndex literalIndex) = _
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
      simp [representativeRoute, metadataLookup, routeTerminalVector]
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
      unfold PositionedPeriodicCNF.normalizeIncidenceRoute
      rw [routeTerminalVector_map_sub]
      unfold representativeRoute
      rw [metadataLookup]
      rw [representativeClauseIndex_eq source clause.literals]

/-- The first normalized representative route and its underlying raw local
metadata route have the same complete terminal vector. -/
theorem representativeRoute_routeTerminalVector_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    routeTerminalVector
        (representativeRoute source clauseIndex literalIndex) =
      routeTerminalVector
        (rawRepresentativeRoute source clauseIndex literalIndex) := by
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
      unfold PositionedPeriodicCNF.normalizeIncidenceRoute
      exact routeTerminalVector_map_sub _ _

/-- Therefore the complete final retained route and its raw representative
metadata route have the same terminal vector. -/
theorem incidenceRoutes_routeTerminalVector_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    routeTerminalVector
        (FormulaShapeRetainedPlanarDirection.incidenceRoutes
          source clauseIndex literalIndex) =
      routeTerminalVector
        (rawRepresentativeRoute source clauseIndex literalIndex) :=
  (incidenceRoutes_routeTerminalVector_eq_representativeRoute
    source clauseIndex literalIndex).trans
      (representativeRoute_routeTerminalVector_eq_rawRepresentativeRoute
        source clauseIndex literalIndex)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
