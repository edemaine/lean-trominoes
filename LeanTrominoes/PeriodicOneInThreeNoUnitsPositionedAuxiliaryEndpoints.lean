/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsAuxiliaryIncidences
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedNormalizedLocalRoutes
import LeanTrominoes.PositionedPeriodicCNFSumRouteSuffixes

/-!
# Finality of local unit-elimination auxiliary endpoints

Inherited source variables terminate at boundary ports of the local
unit-elimination drawing, but its fresh auxiliaries are placed at their
actual periodic variable positions.  After putting a local route in its
generated clause's anchor gauge, an auxiliary endpoint is therefore already
the final canonical literal endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- Every genuine unit-elimination auxiliary incidence needs only the
singleton suffix at its normalized local endpoint. -/
theorem normalizedLocalEndpoint_auxiliary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx)
    (auxiliary :
      (Nat × PeriodicClause Variable) × OneInThreeNoUnitAux)
    (literalAuxiliary : literal.atom = .inr auxiliary) :
    normalizedLocalEndpoint source sourcePlacement
        clauseIndex literalIndex =
      PositionedPeriodicCNF.canonicalLiteralPosition
        (placement source sourcePlacement) clause literal := by
  rcases formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have generatedClauseMember :
      metadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          metadata.sourceClauseIndex
          metadata.sourceClause.literals := by
    rw [← clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨metadata.clause,
        List.fst_mem_of_mem_zipIdx localClauseMember,
        rfl⟩
  have generatedLiteralMember :
      literal ∈ metadata.clause.literals :=
    List.fst_mem_of_mem_zipIdx metadataLiteralMember
  have auxiliaryData :=
    PeriodicOneInThreeNoUnits.auxiliary_scope_offset_of_mem_clauseClauses
      metadata.sourceClauseIndex
      metadata.sourceClause.literals
      generatedClauseMember generatedLiteralMember
      auxiliary literalAuxiliary
  rcases auxiliary with ⟨scope, kind⟩
  have scopeEqual :
      scope =
        (metadata.sourceClauseIndex,
          metadata.sourceClause.literals) :=
    auxiliaryData.1
  subst scope
  have sourceClauseLookup :
      source.clauses[metadata.sourceClauseIndex]? =
        some metadata.sourceClause :=
    (List.mem_zipIdx_iff_getElem?).mp sourceClauseMember
  have clausePositionEqual :
      source.clausePosition metadata.sourceClauseIndex =
        metadata.sourceClause.position := by
    simp [PositionedPeriodicCNF.clausePosition,
      sourceClauseLookup]
  subst clause
  simp only [normalizedLocalEndpoint, metadataLookup]
  rw [(List.mem_zipIdx_iff_getElem?).mp metadataLiteralMember]
  simp only
  rw [literalAuxiliary,
    PlanarOneInThreeNoUnits.instantiatedDrawing_auxiliaryPosition]
  have literalOffset :
      literal.offset =
        PeriodicOneInThree.anchor
          metadata.sourceClause.literals :=
    auxiliaryData.2
  apply Prod.ext <;>
  simp [PositionedPeriodicCNF.canonicalLiteralPosition,
    placement, auxiliaryOccurrencePosition,
    PeriodicVariablePlacement.translation,
    gadgetScale, literalAuxiliary, clausePositionEqual,
    literalOffset, Cell.add, Cell.sub, Cell.scale]
  <;> ring

/-- Complete an inherited unit-elimination suffix family by assigning
singleton suffixes to every fresh auxiliary incidence. -/
def completeRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement)) :
    PositionedPeriodicCNF.CanonicalIncidenceRouteSuffixes
      (formula source)
      (placement source sourcePlacement)
      (normalizedLocalEndpoint source sourcePlacement) :=
  PositionedPeriodicCNF.completeSumIncidenceRouteSuffixes
    (formula source)
    (placement source sourcePlacement)
    (normalizedLocalEndpoint source sourcePlacement)
    inherited
    (by
      intro clause clauseIndex clauseMember
        literal literalIndex literalMember
        auxiliary literalAuxiliary
      exact normalizedLocalEndpoint_auxiliary
        source sourcePlacement clauseMember literalMember
        auxiliary literalAuxiliary)

/-- Unit-elimination local routes spliced to an inherited suffix family,
with fresh auxiliaries completed automatically. -/
def splicedRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement)) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.spliceLocalIncidenceRoutes
    (normalizedLocalRoutes source sourcePlacement)
    (completeRouteSuffixes source sourcePlacement inherited)

/-- Under the local unit-elimination hypotheses, splicing any valid inherited
suffix family produces canonical orthogonal routes for every output
incidence. -/
theorem splicedRoutes_valid_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    (splicedRoutes source sourcePlacement inherited
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement source sourcePlacement) clause) ∧
      (splicedRoutes source sourcePlacement inherited
        clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (placement source sourcePlacement) clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (splicedRoutes source sourcePlacement inherited
          clauseIndex literalIndex) := by
  simpa [splicedRoutes] using
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes_valid_of_members
      (normalizedLocalRoutes source sourcePlacement)
      (completeRouteSuffixes source sourcePlacement inherited)
      clauseMember literalMember
      (normalizedLocalRoutes_endpoints_of_members
        source sourcePlacement sourceWidth sourceDistinct
        clauseMember literalMember)
      (normalizedLocalRoutes_orthogonal_of_members
        source sourcePlacement sourceWidth sourceDistinct
        clauseMember literalMember)

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
