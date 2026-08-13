/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDrawingCompatibility

/-!
# Fundamental-square bounds for normalized non-carrier routes

Clause-anchor normalization subtracts one physical period translation from
every point of a retained local route.  For crossover, bend, routed-clause,
and routed-variable components, the clause and every route point lie in the
same macrocell.  Their period quotients therefore agree, so normalization is
exactly coordinatewise remainder and every resulting route point lies in the
closed canonical square.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

theorem normalizePoint_eq_emod_of_canonical_eq_of_quotient_eq
    {period : Int}
    {clausePosition point translation : Cell}
    (canonical :
      Cell.sub clausePosition translation =
        (clausePosition.1 % period, clausePosition.2 % period))
    (quotients :
      clausePosition.1 / period = point.1 / period ∧
        clausePosition.2 / period = point.2 / period) :
    Cell.sub point translation =
      (point.1 % period, point.2 % period) := by
  rcases clausePosition with ⟨clauseX, clauseY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases translation with ⟨translationX, translationY⟩
  simp only [Cell.sub, Prod.mk.injEq] at canonical ⊢
  change
    clauseX / period = pointX / period ∧
      clauseY / period = pointY / period at quotients
  have clauseXDivision := Int.emod_add_mul_ediv clauseX period
  have clauseYDivision := Int.emod_add_mul_ediv clauseY period
  have pointXDivision := Int.emod_add_mul_ediv pointX period
  have pointYDivision := Int.emod_add_mul_ediv pointY period
  have horizontalMul :=
    congrArg (fun quotient => period * quotient) quotients.1
  have verticalMul :=
    congrArg (fun quotient => period * quotient) quotients.2
  constructor <;> omega

theorem metadata_normalizedRoutePoint_eq_emod_of_noncarrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula = some center)
    (nonempty : metadata.clause.literals ≠ [])
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex) :
    Cell.sub point
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation
          (PeriodicCNF.clauseAnchor
            ((wrapPeriodicPlanarSATClause
              (periodicizePlanarSATClause formula
                metadata.clause)).variableGauge
                  (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                    formula)))) =
      (point.1 %
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period,
        point.2 %
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period) := by
  have notCarrier :
      ¬∃ link, metadata.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at centerEq
    simp [DrawingPlanarSATComponent.macrocellCenter] at centerEq
  have originalValid : metadata.Valid formula :=
    metadata.valid_of_retainedValid_of_not_carrier valid notCarrier
  have clauseBounds :=
    metadata.retainedClausePosition_in_macrocell
      wellFormed degree isLocal valid center centerEq nonempty
  have pointBounds :=
    metadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal originalValid center centerEq
      literalMember pointMember
  have quotients :=
    macrocellQuotient_eq
      (periodFactor :=
        drawingGridSize (PeriodicCNF.incidenceGraph formula))
      clauseBounds pointBounds
  apply normalizePoint_eq_emod_of_canonical_eq_of_quotient_eq
  · simpa [PositionedPeriodicCNF.canonicalClausePosition,
      clauseResidue,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      metadata_canonicalClausePosition_eq_residue
        wellFormed degree isLocal metadata valid nonempty
  · simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement,
      drawingPeriodicPlanarSATPlacement, planarMacroScale] using quotients

theorem metadata_normalizedRoutePoint_inFundamental_of_noncarrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula = some center)
    (nonempty : metadata.clause.literals ≠ [])
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex) :
    let normalized :=
      Cell.sub point
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation
          (PeriodicCNF.clauseAnchor
            ((wrapPeriodicPlanarSATClause
              (periodicizePlanarSATClause formula
                metadata.clause)).variableGauge
                  (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                    formula))))
    0 ≤ normalized.1 ∧
      normalized.1 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period ∧
      0 ≤ normalized.2 ∧
      normalized.2 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
  dsimp only
  rw [metadata_normalizedRoutePoint_eq_emod_of_noncarrier
    wellFormed degree isLocal metadata valid center centerEq nonempty
    literalMember pointMember]
  have periodPositive :
      (0 : Int) <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
    exact_mod_cast
      drawingPeriodicPlanarSATPlacement_period_pos formula
  exact
    ⟨Int.emod_nonneg _ (ne_of_gt periodPositive),
      Int.emod_lt_of_pos _ periodPositive,
      Int.emod_nonneg _ (ne_of_gt periodPositive),
      Int.emod_lt_of_pos _ periodPositive⟩

end LeanTrominoes.PeriodicOrthocrossing
