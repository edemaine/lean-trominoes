/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCompleteRouteCertificates
import LeanTrominoes.PeriodicCNFPlanarRetainedCertificate
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATRasterizedDrawing
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedTerminalDirections
import LeanTrominoes.RetainedAngularDirectionProfile

/-!
# Canonical orthogonal drawing for the refined retained fixed-eight split

The endpoint and orthogonality theorems for the complete retained fan route
family fit the standard `CanonicalOrthogonalIncidenceRoutes` interface.  This
file constructs that package first generically and then for the final
retained planar-SAT source.  Its canonical interface is the input needed by
later whole-drawing compatibility and planarity layers.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Package a retained source route family and its terminal certificates as
canonical orthogonal routes for the refined fixed-eight formula. -/
def retainedAngularFanRefinedCanonicalOrthogonalRoutes
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
            (routes clauseIndex literalIndex)) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedAngularFanRefinedFormula
        source placement routes)
      (retainedAngularFanRefinedPlacement placement) where
  routes :=
    retainedAngularFanSplicedIncidenceRoutes
      source placement routes
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact retainedAngularFanRefinedIncidenceRoutes_endpoints
      source placement routes fits certificate
      endpoints lengths retainedRoutes
      clauseMember literalMember
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact retainedAngularFanRefinedIncidenceRoutes_orthogonal
      source placement routes fits certificate
      endpoints lengths retainedRoutes
      clauseMember literalMember

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Every genuine route of the specialized refined retained split has its
canonical clause and literal endpoints. -/
theorem
    retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingRefinedEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingRefinedEightOccurrenceSplitPlacement
              source)
            clause) ∧
      (retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (retainedDrawingRefinedEightOccurrenceSplitPlacement
                source)
              clause literal) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source sourceClausesNonempty
  apply retainedAngularFanRefinedIncidenceRoutes_endpoints
  · simpa [retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula] using
      retainedDrawingAngularOccurrenceOrder_fitsEightSlots
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        clauseMember literalMember
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
        clauseMember literalMember
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
        (clause, clauseIndex) clauseMember
        (literal, literalIndex) literalMember
  · exact clauseMember
  · exact literalMember

/-- Every genuine route of the specialized refined retained split is
orthogonal. -/
theorem
    retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingRefinedEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    OrthogonalPolyline
      (retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source sourceClausesNonempty
  apply retainedAngularFanRefinedIncidenceRoutes_orthogonal
  · simpa [retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula] using
      retainedDrawingAngularOccurrenceOrder_fitsEightSlots
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
  · intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        sourceClauseMember sourceLiteralMember
  · intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
        sourceClauseMember sourceLiteralMember
  · intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
        (sourceClause, sourceClauseIndex) sourceClauseMember
        (sourceLiteral, sourceLiteralIndex) sourceLiteralMember
  · exact clauseMember
  · exact literalMember

/-- The complete refined retained route family packaged with canonical
endpoints and pointwise orthogonality. -/
def
    retainedDrawingRefinedEightOccurrenceSplitCanonicalOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedDrawingRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingRefinedEightOccurrenceSplitPlacement
        source) where
  routes :=
    retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes source
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes_endpoints
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes_orthogonal
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
