import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedSplicedRouteIsolation
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedSplicedRouteSeparation

/-!
# Pairwise separation data for inherited unit-elimination routes

Inherited local routes in one source-clause block end at distinct indexed
boundary ports.  This file combines that port arithmetic with the finite
local drawing's ordinary avoidance certificate to show that any remaining
listed contact can occur only at the two generated clause heads.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The source-tail part of two inherited suffixes in one source block
inherits ordinary separation and tail-only contacts from the corresponding
simple source routes. -/
theorem inheritedSourceRoute_tails_separated_of_inheritedData_same_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      InheritedIncidenceData source sourcePlacement
        firstClauseIndex firstLiteralIndex)
    (second :
      InheritedIncidenceData source sourcePlacement
        secondClauseIndex secondLiteralIndex)
    (sameSource :
      first.sourceClauseIndex = second.sourceClauseIndex)
    (sourceAvoid :
      RoutesAvoidEachOther
        (sourceRoutes
          first.sourceClauseIndex first.sourceLiteralIndex)
        (sourceRoutes
          second.sourceClauseIndex second.sourceLiteralIndex))
    (firstNodup :
      (sourceRoutes
        first.sourceClauseIndex first.sourceLiteralIndex).Nodup)
    (secondNodup :
      (sourceRoutes
        second.sourceClauseIndex second.sourceLiteralIndex).Nodup) :
    RoutesAvoidEachOther
        (inheritedSourceRoute
          (placement source sourcePlacement) sourcePlacement
          first.sourceClause first.generatedClause
          (sourceRoutes
            first.sourceClauseIndex first.sourceLiteralIndex)).tail
        (inheritedSourceRoute
          (placement source sourcePlacement) sourcePlacement
          second.sourceClause second.generatedClause
          (sourceRoutes
            second.sourceClauseIndex second.sourceLiteralIndex)).tail ∧
      RoutesMeetOnlyAtTails
        (inheritedSourceRoute
          (placement source sourcePlacement) sourcePlacement
          first.sourceClause first.generatedClause
          (sourceRoutes
            first.sourceClauseIndex first.sourceLiteralIndex)).tail
        (inheritedSourceRoute
          (placement source sourcePlacement) sourcePlacement
          second.sourceClause second.generatedClause
          (sourceRoutes
            second.sourceClauseIndex second.sourceLiteralIndex)).tail :=
  inheritedSourceRoute_tails_separated_of_common_shift
    (placement source sourcePlacement) sourcePlacement
    first.sourceClause second.sourceClause
    first.generatedClause second.generatedClause
    (sourceRoutes
      first.sourceClauseIndex first.sourceLiteralIndex)
    (sourceRoutes
      second.sourceClauseIndex second.sourceLiteralIndex)
    (first.sourceRouteShifts_eq_of_source_index_eq
      source sourcePlacement second sameSource)
    sourceAvoid firstNodup secondNodup

/-- Two inherited normalized local routes in one source block can meet only
at their clause-side heads when their recovered source occurrence indices
are distinct. -/
theorem normalizedLocalRoutes_meetOnlyAtHeads_of_inherited_same_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {firstClause secondClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (formula source).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (formula source).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    {firstMetadata secondMetadata : ClauseMetadata Variable}
    (firstLookup :
      (formulaClauseMetadata source)[firstClauseIndex]? =
        some firstMetadata)
    (secondLookup :
      (formulaClauseMetadata source)[secondClauseIndex]? =
        some secondMetadata)
    (sameSource :
      firstMetadata.sourceClauseIndex =
        secondMetadata.sourceClauseIndex)
    (globalIncidencesDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex)
    {firstSourceLiteral secondSourceLiteral : PeriodicLiteral Variable}
    {firstSourceLiteralIndex secondSourceLiteralIndex : Nat}
    (firstSourceLiteralMember :
      (firstSourceLiteral, firstSourceLiteralIndex) ∈
        firstMetadata.sourceClause.literals.zipIdx)
    (secondSourceLiteralMember :
      (secondSourceLiteral, secondSourceLiteralIndex) ∈
        secondMetadata.sourceClause.literals.zipIdx)
    (firstLiteralAtom :
      firstLiteral.atom = .inl firstSourceLiteral.atom)
    (secondLiteralAtom :
      secondLiteral.atom = .inl secondSourceLiteral.atom)
    (sourceIndicesDistinct :
      firstSourceLiteralIndex ≠ secondSourceLiteralIndex) :
    RoutesMeetOnlyAtHeads
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      (normalizedLocalRoutes source sourcePlacement
        secondClauseIndex secondLiteralIndex) := by
  rcases formulaClauseMetadata_lookup_valid
      source firstClauseMember with
    ⟨actualFirst, actualFirstLookup, firstClauseEqual,
      firstSourceMember, firstLocalMember⟩
  have actualFirstEqual : actualFirst = firstMetadata := by
    apply Option.some.inj
    exact actualFirstLookup.symm.trans firstLookup
  subst actualFirst
  rcases formulaClauseMetadata_lookup_valid
      source secondClauseMember with
    ⟨actualSecond, actualSecondLookup, secondClauseEqual,
      secondSourceMember, secondLocalMember⟩
  have actualSecondEqual : actualSecond = secondMetadata := by
    apply Option.some.inj
    exact actualSecondLookup.symm.trans secondLookup
  subst actualSecond
  subst firstClause
  subst secondClause
  have taggedSourcesEqual :
      (firstMetadata.sourceClause,
          firstMetadata.sourceClauseIndex) =
        (secondMetadata.sourceClause,
          secondMetadata.sourceClauseIndex) :=
    PeriodicOrthocrossing.tagged_eq_of_mem_zipIdx_of_snd_eq
      firstSourceMember secondSourceMember sameSource
  have sourceClausesEqual :
      firstMetadata.sourceClause = secondMetadata.sourceClause :=
    congrArg Prod.fst taggedSourcesEqual
  have firstGeneratedMember :
      firstMetadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          firstMetadata.sourceClauseIndex
          firstMetadata.sourceClause.literals := by
    rw [← clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨firstMetadata.clause,
        List.fst_mem_of_mem_zipIdx firstLocalMember, rfl⟩
  have secondGeneratedMember :
      secondMetadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          secondMetadata.sourceClauseIndex
          secondMetadata.sourceClause.literals := by
    rw [← clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨secondMetadata.clause,
        List.fst_mem_of_mem_zipIdx secondLocalMember, rfl⟩
  have firstAnchor :=
    PeriodicOneInThreeNoUnits.clauseAnchor_eq_of_mem_clauseClauses
      firstMetadata.sourceClauseIndex
      firstMetadata.sourceClause.literals
      firstMetadata.clause.literals firstGeneratedMember
  have secondAnchor :=
    PeriodicOneInThreeNoUnits.clauseAnchor_eq_of_mem_clauseClauses
      secondMetadata.sourceClauseIndex
      secondMetadata.sourceClause.literals
      secondMetadata.clause.literals secondGeneratedMember
  have anchorsEqual :
      PeriodicCNF.clauseAnchor firstMetadata.clause.literals =
        PeriodicCNF.clauseAnchor secondMetadata.clause.literals := by
    rw [sourceClausesEqual] at firstAnchor
    simpa [PeriodicCNF.clauseAnchor,
      PeriodicOneInThree.anchor] using
      firstAnchor.trans secondAnchor.symm
  have firstSourceMemberPlain :
      firstMetadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx firstSourceMember
  have secondSourceMemberPlain :
      secondMetadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx secondSourceMember
  have firstArityAtMostThree :
      firstMetadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth firstMetadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨firstMetadata.sourceClause, firstSourceMemberPlain, rfl⟩
  have secondArityAtMostThree :
      secondMetadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth secondMetadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨secondMetadata.sourceClause, secondSourceMemberPlain, rfl⟩
  have firstSourceIndexLt :=
    (List.mem_zipIdx' firstSourceLiteralMember).1
  have secondSourceIndexLt :=
    (List.mem_zipIdx' secondSourceLiteralMember).1
  have firstSourceIndexLtThree : firstSourceLiteralIndex < 3 := by
    omega
  have secondSourceIndexLtThree : secondSourceLiteralIndex < 3 := by
    omega
  have firstArityPositive :
      0 < firstMetadata.sourceClause.literals.length :=
    Nat.zero_lt_of_lt firstSourceIndexLt
  have secondArityPositive :
      0 < secondMetadata.sourceClause.literals.length :=
    Nat.zero_lt_of_lt secondSourceIndexLt
  have firstEndpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      firstClauseMember firstLiteralMember
  have secondEndpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      secondClauseMember secondLiteralMember
  have firstLocalEndpoint :=
    normalizedLocalEndpoint_eq_normalizedSourcePort
      source sourcePlacement sourceWidth sourceDistinct
      firstLookup firstLiteralMember
      firstSourceLiteralMember firstLiteralAtom
  have secondLocalEndpoint :=
    normalizedLocalEndpoint_eq_normalizedSourcePort
      source sourcePlacement sourceWidth sourceDistinct
      secondLookup secondLiteralMember
      secondSourceLiteralMember secondLiteralAtom
  have firstHeadPoint :=
    canonicalClausePosition_eq_normalizedSourceClausePosition_add_local
      source sourcePlacement sourceWidth sourceDistinct
      firstLookup firstLiteralMember
      firstSourceLiteralMember firstLiteralAtom
  have secondHeadPoint :=
    canonicalClausePosition_eq_normalizedSourceClausePosition_add_local
      source sourcePlacement sourceWidth sourceDistinct
      secondLookup secondLiteralMember
      secondSourceLiteralMember secondLiteralAtom
  have originsEqual :
      normalizedSourceClausePosition
          (placement source sourcePlacement)
          firstMetadata.sourceClause firstMetadata.clause =
        normalizedSourceClausePosition
          (placement source sourcePlacement)
          secondMetadata.sourceClause secondMetadata.clause := by
    rw [sourceClausesEqual]
    exact normalizedSourceClausePosition_eq_of_anchor_eq
      (placement source sourcePlacement)
      secondMetadata.sourceClause
      firstMetadata.clause secondMetadata.clause anchorsEqual
  have firstHeadSecondLastNe :
      PositionedPeriodicCNF.canonicalClausePosition
          (placement source sourcePlacement) firstMetadata.clause ≠
        normalizedSourcePort
          (placement source sourcePlacement)
          secondMetadata.sourceClause secondMetadata.clause
          secondSourceLiteralIndex := by
    rw [firstHeadPoint]
    intro equal
    unfold normalizedSourcePort at equal
    rw [originsEqual] at equal
    rw [sourceClausesEqual] at equal
    exact
      sourceLocalClausePosition_ne_sourceLocalPosition
        secondMetadata.sourceClause.literals.length
        secondSourceLiteralIndex secondArityPositive
        secondArityAtMostThree secondSourceIndexLt
        (Cell.add_left_injective _ equal)
  have firstLastSecondHeadNe :
      normalizedSourcePort
          (placement source sourcePlacement)
          firstMetadata.sourceClause firstMetadata.clause
          firstSourceLiteralIndex ≠
        PositionedPeriodicCNF.canonicalClausePosition
          (placement source sourcePlacement) secondMetadata.clause := by
    rw [secondHeadPoint]
    intro equal
    unfold normalizedSourcePort at equal
    rw [originsEqual] at equal
    exact
      sourceLocalClausePosition_ne_sourceLocalPosition
        secondMetadata.sourceClause.literals.length
        firstSourceLiteralIndex secondArityPositive
        secondArityAtMostThree (by simpa [← sourceClausesEqual])
        (Cell.add_left_injective _ equal).symm
  have lastsNe :
      normalizedSourcePort
          (placement source sourcePlacement)
          firstMetadata.sourceClause firstMetadata.clause
          firstSourceLiteralIndex ≠
        normalizedSourcePort
          (placement source sourcePlacement)
          secondMetadata.sourceClause secondMetadata.clause
          secondSourceLiteralIndex := by
    intro equal
    apply sourceIndicesDistinct
    rw [sourceClausesEqual] at equal
    exact normalizedSourcePort_injective_of_anchor_eq
      (placement source sourcePlacement)
      secondMetadata.sourceClause
      firstMetadata.clause secondMetadata.clause
      firstSourceIndexLtThree secondSourceIndexLtThree
      anchorsEqual equal
  have avoid :=
    normalizedLocalRoutes_avoidEachOther_of_members_of_same_source_of_global_distinct
      source sourcePlacement sourceWidth sourceDistinct
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstLookup secondLookup sameSource globalIncidencesDistinct
  apply avoid.meetOnlyAtHeads_of_endpoints_ne
  · rw [firstEndpoints.1, secondEndpoints.2,
      secondLocalEndpoint]
    exact fun equal => firstHeadSecondLastNe (Option.some.inj equal)
  · rw [firstEndpoints.2, secondEndpoints.1,
      firstLocalEndpoint]
    exact fun equal => firstLastSecondHeadNe (Option.some.inj equal)
  · rw [firstEndpoints.2, secondEndpoints.2,
      firstLocalEndpoint, secondLocalEndpoint]
    exact fun equal => lastsNe (Option.some.inj equal)

/-- The proof-backed inherited selectors automatically supply all provenance
needed by the head-only local-contact theorem. -/
theorem normalizedLocalRoutes_meetOnlyAtHeads_of_inheritedData_same_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      InheritedIncidenceData source sourcePlacement
        firstClauseIndex firstLiteralIndex)
    (second :
      InheritedIncidenceData source sourcePlacement
        secondClauseIndex secondLiteralIndex)
    (sameSource :
      first.sourceClauseIndex = second.sourceClauseIndex)
    (generatedDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesMeetOnlyAtHeads
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      (normalizedLocalRoutes source sourcePlacement
        secondClauseIndex secondLiteralIndex) := by
  have firstSourceLiteralMember :
      (first.sourceLiteral, first.sourceLiteralIndex) ∈
        first.metadata.sourceClause.literals.zipIdx := by
    simpa [first.metadataSourceClause] using
      first.sourceLiteralMember
  have secondSourceLiteralMember :
      (second.sourceLiteral, second.sourceLiteralIndex) ∈
        second.metadata.sourceClause.literals.zipIdx := by
    simpa [second.metadataSourceClause] using
      second.sourceLiteralMember
  have metadataSameSource :
      first.metadata.sourceClauseIndex =
        second.metadata.sourceClauseIndex := by
    rw [first.metadataSourceClauseIndex,
      second.metadataSourceClauseIndex]
    exact sameSource
  have sourceCoordinatesDistinct :=
    first.sourceCoordinatesDistinct_of_generatedDistinct
      source sourcePlacement second generatedDistinct
  have sourceIndicesDistinct :
      first.sourceLiteralIndex ≠ second.sourceLiteralIndex :=
    sourceCoordinatesDistinct.resolve_left (fun ne => ne sameSource)
  apply
    normalizedLocalRoutes_meetOnlyAtHeads_of_inherited_same_source
      source sourcePlacement sourceWidth sourceDistinct
      first.generatedClauseMember second.generatedClauseMember
      first.generatedLiteralMember second.generatedLiteralMember
      first.metadataLookup second.metadataLookup
      metadataSameSource generatedDistinct
      firstSourceLiteralMember secondSourceLiteralMember
  · simpa [first.metadataClause] using first.literalAtom
  · simpa [second.metadataClause] using second.literalAtom
  · exact sourceIndicesDistinct

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
