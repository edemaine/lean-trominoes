import LeanTrominoes.PeriodicPlanarThreeDMIncidenceRouting
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDrawing

/-!
# Transport of rebased periodic CNF incidence routes

The planar 3DM reduction reverses each stored clause-to-variable route and
rebases it at its variable endpoint.  Two presentation changes used by the
exact-one construction alter the stored canonical representative:

* clause-direction ordering reindexes a route and changes its clause-anchor
  gauge; and
* variable gauging changes both the clause anchor and the variable
  representative.

This module records the cancellations after reversal and rebasing.  Clause
ordering leaves the physical rebased route unchanged.  Variable gauging
translates it by the inverse gauge shift, exactly as it translates the stored
variable representative.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- After clause-direction ordering, reversal and rebasing cancel the
whole-period clause-anchor translation.  The result is exactly the rebased
source route selected by the stable literal permutation. -/
theorem exists_sourceLiteral_of_orderCanonicalRoutes_rebasedRoute_eq
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {orderedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (orderedClause, clauseIndex) ∈
        (orderClausesByRouteDirection source routes).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ orderedClause.literals.zipIdx) :
    ∃ sourceClause sourceLiteral sourceLiteralIndex,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
        (sourceLiteral, sourceLiteralIndex) ∈
          sourceClause.literals.zipIdx ∧
        literal = sourceLiteral ∧
        PeriodicOrthocrossing.translatePolyline
            (placement.translation
              (Cell.sub
                (PeriodicCNF.clauseAnchor orderedClause.literals)
                literal.offset))
            (orderCanonicalRoutesByClauseDirection
              source placement routes clauseIndex literalIndex).reverse =
          PeriodicOrthocrossing.translatePolyline
            (placement.translation
              (Cell.sub
                (PeriodicCNF.clauseAnchor sourceClause.literals)
                sourceLiteral.offset))
            (routes clauseIndex sourceLiteralIndex).reverse := by
  rcases exists_sourceLiteral_of_orderedLiteral_mem
      routes clauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember,
      orderedClauseEq, literalEq, orderedRouteEq⟩
  refine
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember, literalEq, ?_⟩
  subst orderedClause
  subst literal
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  rw [orderCanonicalRoutesByClauseDirection,
    sourceClauseLookup, orderedRouteEq]
  rw [show
    (PeriodicOrthocrossing.translatePolyline
        (placement.translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor sourceClause.literals)
            (PeriodicCNF.clauseAnchor
              (orderClauseByRouteDirection
                routes clauseIndex sourceClause).literals)))
        (routes clauseIndex sourceLiteralIndex)).reverse =
      PeriodicOrthocrossing.translatePolyline
        (placement.translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor sourceClause.literals)
            (PeriodicCNF.clauseAnchor
              (orderClauseByRouteDirection
                routes clauseIndex sourceClause).literals)))
        (routes clauseIndex sourceLiteralIndex).reverse by
    simp [PeriodicOrthocrossing.translatePolyline]]
  simp only [PeriodicOrthocrossing.translatePolyline, List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases point with ⟨pointX, pointY⟩
  rcases PeriodicCNF.clauseAnchor sourceClause.literals with
    ⟨sourceAnchorX, sourceAnchorY⟩
  rcases PeriodicCNF.clauseAnchor
      (orderClauseByRouteDirection
        routes clauseIndex sourceClause).literals with
    ⟨orderedAnchorX, orderedAnchorY⟩
  rcases sourceLiteral.offset with ⟨literalX, literalY⟩
  apply Prod.ext <;>
    simp [PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- Reversal and rebasing of a canonically transported variable-gauge route
equals the old rebased route translated by the inverse physical gauge. -/
theorem variableGaugeCanonicalIncidenceRoutes_rebasedRoute_eq
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat} :
    PeriodicOrthocrossing.translatePolyline
        ((placement.variableGauge gauge).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor
              (clause.literals.variableGauge gauge))
            (literal.variableGauge gauge).offset))
        (variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes
          clauseIndex literalIndex).reverse =
      PeriodicOrthocrossing.translatePolyline
        (placement.translation
          (Cell.sub (0, 0) (gauge literal.atom)))
        (PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (Cell.sub
              (PeriodicCNF.clauseAnchor clause.literals)
              literal.offset))
          (routes clauseIndex literalIndex).reverse) := by
  rw [variableGaugeCanonicalIncidenceRoutes_of_clause_mem
    source placement gauge routes clauseMember]
  rw [show
    (PeriodicOrthocrossing.translatePolyline
        (placement.translation
          (variableGaugeCanonicalRouteShift gauge clause))
        (routes clauseIndex literalIndex)).reverse =
      PeriodicOrthocrossing.translatePolyline
        (placement.translation
          (variableGaugeCanonicalRouteShift gauge clause))
        (routes clauseIndex literalIndex).reverse by
    simp [PeriodicOrthocrossing.translatePolyline]]
  simp only [PeriodicOrthocrossing.translatePolyline, List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases point with ⟨pointX, pointY⟩
  rcases literal with ⟨atom, ⟨literalX, literalY⟩, value⟩
  cases sourceAnchorEq : PeriodicCNF.clauseAnchor clause.literals with
  | mk sourceAnchorX sourceAnchorY =>
  cases gaugedAnchorEq : PeriodicCNF.clauseAnchor
      (clause.literals.variableGauge gauge) with
  | mk gaugedAnchorX gaugedAnchorY =>
  cases gaugeEq : gauge atom with
  | mk gaugeX gaugeY =>
  apply Prod.ext <;>
    simp [PeriodicVariablePlacement.variableGauge,
      PeriodicVariablePlacement.translation,
      PeriodicLiteral.variableGauge,
      variableGaugeCanonicalRouteShift,
      sourceAnchorEq, gaugedAnchorEq, gaugeEq,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

end PositionedPeriodicCNF
end LeanTrominoes
