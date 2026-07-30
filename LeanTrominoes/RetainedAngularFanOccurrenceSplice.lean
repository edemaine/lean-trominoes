import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.RetainedAngularFanBoundaryRouteFamily

/-!
# Retained source incidences through refined angular fans

The retained source router reaches the factor-eight boundary of a Figure 7
fan.  Scaling the already certified local fan spoke by the same factor makes
its first point coincide with that boundary.  This file joins the two pieces,
first for one genuine source incidence and then as a total clause/literal
lookup.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Join one retained source-to-boundary route to the factor-eight copy of
its certified local Figure 7 fan spoke. -/
def retainedAngularFanSplicedOccurrenceRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  joinAtEndpoint
    (retainedAngularFanBoundaryIncidenceRoutes
      source routes clauseIndex literalIndex)
    (scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        clause literal clauseIndex literalIndex))

/-- Every genuine retained occurrence splice starts at the scale-288 source
clause, ends at the factor-eight copied literal, and is orthogonal. -/
theorem retainedAngularFanSplicedOccurrenceRoute_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source.erase routes))
    (certificate :
      RetainedOccurrenceTerminalCertificate
        source.erase routes)
    (endpoints :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          (routes clauseIndex literalIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  placement clause) ∧
            (routes clauseIndex literalIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  placement clause literal))
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (retainedRoutes :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          RetainedRayPolyline
            (routes clauseIndex literalIndex))
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedAngularFanSplicedOccurrenceRoute
      source placement routes clause literal
      clauseIndex literalIndex).head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement
            (PositionedPeriodicCNF.canonicalClausePosition
              placement clause)) ∧
      (retainedAngularFanSplicedOccurrenceRoute
        source placement routes clause literal
        clauseIndex literalIndex).getLast? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (PeriodicEightOccurrenceSplitPositioned.placement
                  placement)
                (PeriodicEightOccurrenceSplitPositioned.occurrenceClause
                  (occurrencePortsOfAngularOrder
                    source.erase
                    (angularOccurrenceOrder source.erase routes))
                  clauseIndex clause)
                (occurrenceLiteral
                  (occurrencePortsOfAngularOrder
                    source.erase
                    (angularOccurrenceOrder source.erase routes))
                  clauseIndex literalIndex literal))) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedAngularFanSplicedOccurrenceRoute
          source placement routes clause literal
          clauseIndex literalIndex) := by
  have boundaryValid :=
    retainedAngularFanBoundaryIncidenceRoutes_valid
      source placement routes fits certificate
      endpoints lengths retainedRoutes
      clauseMember literalMember
  have suffixHead :=
    angularOccurrenceSuffix_head?
      placement
      (angularOccurrenceOrder source.erase routes)
      clause literal clauseIndex literalIndex
  have suffixLast :=
    angularOccurrenceSuffix_getLast?
      source placement
      (angularOccurrenceOrder source.erase routes)
      clauseMember literalMember
  have scaledSuffixHead :
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          clause literal clauseIndex literalIndex)).head? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryPositionAt
              placement literal.atom
              (incidenceRelativeOffset clause literal)
              (angularOccurrenceIndex
                (angularOccurrenceOrder source.erase routes)
                literal clauseIndex literalIndex))) := by
    simp [suffixHead]
  have scaledSuffixLast :
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          clause literal clauseIndex literalIndex)).getLast? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (PeriodicEightOccurrenceSplitPositioned.placement
                placement)
              (PeriodicEightOccurrenceSplitPositioned.occurrenceClause
                (occurrencePortsOfAngularOrder
                  source.erase
                  (angularOccurrenceOrder source.erase routes))
                clauseIndex clause)
              (occurrenceLiteral
                (occurrencePortsOfAngularOrder
                  source.erase
                  (angularOccurrenceOrder source.erase routes))
                clauseIndex literalIndex literal))) := by
    simpa using congrArg
      (Option.map
        (Cell.scale retainedTerminalFanRoutingRefinement))
      suffixLast
  have scaledSuffixOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            clause literal clauseIndex literalIndex)) := by
    exact
      (angularOccurrenceSuffix_orthogonal
        placement
        (angularOccurrenceOrder source.erase routes)
        clause literal clauseIndex literalIndex).scalePolyline
          (by
            simp [retainedTerminalFanRoutingRefinement])
  unfold retainedAngularFanSplicedOccurrenceRoute
  refine ⟨joinAtEndpoint_head? boundaryValid.1, ?_, ?_⟩
  · exact joinAtEndpoint_getLast?
      boundaryValid.2.1 scaledSuffixHead scaledSuffixLast
  · exact boundaryValid.2.2.joinAtEndpoint
      scaledSuffixOrthogonal
      boundaryValid.2.1 scaledSuffixHead

/-- Total clause/literal lookup for the refined copied-source routes.
Invalid presentation indices receive the empty route. -/
def retainedAngularFanSplicedOccurrenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            retainedAngularFanSplicedOccurrenceRoute
              source placement routes clause literal
              clauseIndex literalIndex

/-- Genuine source indices reduce the total lookup to their explicit
refined occurrence splice. -/
theorem retainedAngularFanSplicedOccurrenceRoutes_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    retainedAngularFanSplicedOccurrenceRoutes
        source placement routes clauseIndex literalIndex =
      retainedAngularFanSplicedOccurrenceRoute
        source placement routes clause literal
        clauseIndex literalIndex := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [retainedAngularFanSplicedOccurrenceRoutes,
    clauseLookup, literalLookup]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
