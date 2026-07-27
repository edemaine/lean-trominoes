import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineAuxiliaryEndpoints
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedRouteFamily
import LeanTrominoes.PositionedPeriodicCNFSumRouteSuffixes

/-!
# Complete composed Figure 9 route families

The outer unit-elimination sum regards every Figure 9 variable as inherited.
Those variables split once more: original source variables need the direct
external suffix, while fresh Figure 9 auxiliaries already terminate at their
composed local endpoint.  After completing that inner split, the generic
outer-sum completion assigns singleton suffixes to the second-stage
auxiliaries as well.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

/-- Route lookup for the outer-inherited class: use the supplied direct
suffix on original source variables and a singleton on every other atom. -/
def firstStageInheritedRouteSuffixesRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement)) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source)).clauses[
          clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            match literal.atom with
            | .inl (.inl _) =>
                original.routes clauseIndex literalIndex
            | _ =>
                [normalizedLocalEndpoint
                  source sourcePlacement clauseIndex literalIndex]

/-- Complete the suffix obligation for every atom inherited by the outer
unit-elimination layer. -/
def firstStageInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement)) :
    PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source))
      (composedPlacement source sourcePlacement)
      (normalizedLocalEndpoint source sourcePlacement) where
  routes :=
    firstStageInheritedRouteSuffixesRoutes
      source sourcePlacement original
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
      figureNineAtom literalInherited
    have clauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp clauseMember
    have literalLookup :=
      (List.mem_zipIdx_iff_getElem?).mp literalMember
    cases figureNineAtom with
    | inl sourceAtom =>
        simpa [firstStageInheritedRouteSuffixesRoutes,
          clauseLookup, literalLookup, literalInherited] using
          original.endpoints
            clause clauseIndex clauseMember
            literal literalIndex literalMember
            sourceAtom literalInherited
    | inr auxiliary =>
        have endpointEqual :=
          normalizedLocalEndpoint_figureNineAuxiliary
            source sourcePlacement sourceWidth sourceDistinct
            clauseMember literalMember auxiliary literalInherited
        simp [firstStageInheritedRouteSuffixesRoutes,
          clauseLookup, literalLookup, literalInherited,
          endpointEqual]
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
      figureNineAtom literalInherited
    have clauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp clauseMember
    have literalLookup :=
      (List.mem_zipIdx_iff_getElem?).mp literalMember
    cases figureNineAtom with
    | inl sourceAtom =>
        simpa [firstStageInheritedRouteSuffixesRoutes,
          clauseLookup, literalLookup, literalInherited] using
          original.orthogonal
            clause clauseIndex clauseMember
            literal literalIndex literalMember
            sourceAtom literalInherited
    | inr auxiliary =>
        simp [firstStageInheritedRouteSuffixesRoutes,
          clauseLookup, literalLookup, literalInherited,
          PeriodicOrthocrossing.OrthogonalPolyline]

/-- Complete direct original-source suffixes with singleton suffixes for
both generations of auxiliaries. -/
def completeRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement)) :
    PositionedPeriodicCNF.CanonicalIncidenceRouteSuffixes
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source))
      (composedPlacement source sourcePlacement)
      (normalizedLocalEndpoint source sourcePlacement) :=
  PositionedPeriodicCNF.completeSumIncidenceRouteSuffixes
    (PeriodicOneInThreeNoUnitsPositioned.formula
      (PeriodicOneInThreePositioned.formula source))
    (composedPlacement source sourcePlacement)
    (normalizedLocalEndpoint source sourcePlacement)
    (firstStageInheritedRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct original)
    (by
      intro clause clauseIndex clauseMember
        literal literalIndex literalMember
        auxiliary literalAuxiliary
      exact normalizedLocalEndpoint_unitAuxiliary
        source sourcePlacement sourceWidth sourceDistinct
        clauseMember literalMember auxiliary literalAuxiliary)

/-- Fully spliced routes for the two-stage composed clause replacement. -/
def splicedRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement)) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.spliceLocalIncidenceRoutes
    (normalizedLocalRoutes source sourcePlacement)
    (completeRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct original)

/-- Every genuine fully spliced incidence has exact canonical endpoints and
is an orthogonal polyline. -/
theorem splicedRoutes_valid_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (splicedRoutes source sourcePlacement sourceWidth sourceDistinct
        original clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (composedPlacement source sourcePlacement) clause) ∧
      (splicedRoutes source sourcePlacement sourceWidth sourceDistinct
        original clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (composedPlacement source sourcePlacement) clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (splicedRoutes source sourcePlacement sourceWidth sourceDistinct
          original clauseIndex literalIndex) := by
  simpa [splicedRoutes] using
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes_valid_of_members
      (normalizedLocalRoutes source sourcePlacement)
      (completeRouteSuffixes
        source sourcePlacement sourceWidth sourceDistinct original)
      clauseMember literalMember
      (normalizedLocalRoutes_endpoints_of_members
        source sourcePlacement sourceWidth sourceDistinct
        clauseMember literalMember)
      (normalizedLocalRoutes_orthogonal_of_members
        source sourcePlacement sourceWidth sourceDistinct
        clauseMember literalMember)

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
