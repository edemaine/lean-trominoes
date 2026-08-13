/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes
import LeanTrominoes.PeriodicOrthocrossingConstruction

/-!
# Periodic occurrences of normalized incidence routes

Clause-anchor normalization subtracts one physical period translation from
every point of a displayed incidence route.  When the resulting route is
lifted at lattice translate `shift`, it is therefore exactly the original
physical route lifted at `shift - anchor`.

These identities are the geometric counterpart of
`PeriodicClause.anchorNormalize_holds_iff`.  They expose the original route
occurrence selected by anchor normalization and clause-orbit deduplication,
so finite drawing certificates can be reused for the infinite periodic lift.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Translating an anchor-normalized route at `shift` gives the original
physical route at `shift - clauseAnchor`. -/
theorem translatePolyline_normalizeIncidenceRoute
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (route : List Cell)
    (shift : Cell) :
    PeriodicOrthocrossing.translatePolyline
        (placement.translation shift)
        (normalizeIncidenceRoute placement clause route) =
      PeriodicOrthocrossing.translatePolyline
        (placement.translation
          (Cell.sub shift
            (PeriodicCNF.clauseAnchor clause.literals)))
        route := by
  unfold PeriodicOrthocrossing.translatePolyline normalizeIncidenceRoute
    PeriodicVariablePlacement.translation
  simp only [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  apply Prod.ext <;>
    simp [Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- Lookup form of the occurrence identity for a route family normalized at
the clause stored at the same presentation index. -/
theorem translatePolyline_anchorNormalizedIncidenceRoutes
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseLookup :
      source.clauses[clauseIndex]? = some clause)
    (literalIndex : Nat)
    (shift : Cell) :
    PeriodicOrthocrossing.translatePolyline
        (placement.translation shift)
        (source.anchorNormalizedIncidenceRoutes
          placement routes clauseIndex literalIndex) =
      PeriodicOrthocrossing.translatePolyline
        (placement.translation
          (Cell.sub shift
            (PeriodicCNF.clauseAnchor clause.literals)))
        (routes clauseIndex literalIndex) := by
  rw [anchorNormalizedIncidenceRoutes, clauseLookup]
  exact
    translatePolyline_normalizeIncidenceRoute
      placement clause (routes clauseIndex literalIndex) shift

/-- If a deduplicated clause is already anchor-normalized, its selected route
is literally the route at the representative source index. -/
theorem deduplicatedIncidenceRoutes_eq_sourceRoute_of_anchor_zero
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseLookup :
      source.deduplicateByLiterals.clauses[clauseIndex]? =
        some clause)
    (anchorZero :
      PeriodicCNF.clauseAnchor clause.literals = (0, 0))
    (literalIndex : Nat) :
    source.deduplicatedIncidenceRoutes
        placement routes clauseIndex literalIndex =
      routes
        (source.representativeClauseIndex clause.literals)
        literalIndex := by
  simp [deduplicatedIncidenceRoutes, clauseLookup,
    normalizeIncidenceRoute, anchorZero,
    PeriodicVariablePlacement.translation,
    Cell.sub, Cell.scale]

/-- Translation form of the anchor-zero deduplication lookup law. -/
theorem translatePolyline_deduplicatedIncidenceRoutes_of_anchor_zero
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseLookup :
      source.deduplicateByLiterals.clauses[clauseIndex]? =
        some clause)
    (anchorZero :
      PeriodicCNF.clauseAnchor clause.literals = (0, 0))
    (literalIndex : Nat)
    (shift : Cell) :
    PeriodicOrthocrossing.translatePolyline
        (placement.translation shift)
        (source.deduplicatedIncidenceRoutes
          placement routes clauseIndex literalIndex) =
      PeriodicOrthocrossing.translatePolyline
        (placement.translation shift)
        (routes
          (source.representativeClauseIndex clause.literals)
          literalIndex) := by
  rw [deduplicatedIncidenceRoutes_eq_sourceRoute_of_anchor_zero
    source placement routes clauseLookup anchorZero literalIndex]

end PositionedPeriodicCNF
end LeanTrominoes
