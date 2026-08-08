import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearanceRouteRadiusBounds
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteBounds
import LeanTrominoes.PeriodicGridDrawingPointBounds

/-!
# Variable-centered radius bounds through the composed Figure 9 routes

The factor-two source clearance leaves two source cells of slack.  After the
factor-72 composed Figure 9 refinement this becomes 144 cells: exactly enough
to absorb any finite local route between a source-clause gauge and a local
auxiliary endpoint.  Original-variable routes need only 73 of those cells for
their ordered exit connector.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicEightOccurrenceSplit

/-- Scaling and translating a bounded source route gives a bounded inherited
route around the corresponding twice-inherited final literal. -/
theorem inheritedSourceRoute_point_withinCanonicalLiteralRadius
    {Variable : Type*} [DecidableEq Variable]
    {radius : Nat}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceLiteral : PeriodicLiteral Variable)
    (generatedLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceRoute : List Cell)
    (sourceBounds :
      ∀ sourcePoint ∈ sourceRoute,
        WithinCoordinateRadius radius
          (PositionedPeriodicCNF.canonicalLiteralPosition
            sourcePlacement sourceClause sourceLiteral)
          sourcePoint)
    (literalAtom :
      generatedLiteral.atom = .inl (.inl sourceLiteral.atom))
    (literalOffset :
      generatedLiteral.offset = sourceLiteral.offset)
    {point : Cell}
    (pointMember :
      point ∈
        inheritedSourceRoute
          (composedPlacement source sourcePlacement)
          sourcePlacement sourceClause generatedClause sourceRoute) :
    WithinCoordinateRadius (72 * radius)
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (composedPlacement source sourcePlacement)
        generatedClause generatedLiteral)
      point := by
  unfold inheritedSourceRoute at pointMember
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨scaledPoint, scaledPointMember, pointEq⟩
  unfold scalePolyline at scaledPointMember
  rcases List.mem_map.mp scaledPointMember with
    ⟨sourcePoint, sourcePointMember, scaledPointEq⟩
  subst scaledPoint
  subst point
  have scaled :=
    (sourceBounds sourcePoint sourcePointMember).scale 72
  have translated := scaled.translate
    (inheritedSourceRouteShift
      (composedPlacement source sourcePlacement)
      sourcePlacement sourceClause generatedClause)
  have centerEq :
      Cell.add
          (inheritedSourceRouteShift
            (composedPlacement source sourcePlacement)
            sourcePlacement sourceClause generatedClause)
          (Cell.scale (72 : Int)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              sourcePlacement sourceClause sourceLiteral)) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (composedPlacement source sourcePlacement)
          generatedClause generatedLiteral := by
    apply Prod.ext <;>
    simp [inheritedSourceRouteShift,
      normalizedSourceClausePosition,
      PositionedPeriodicCNF.canonicalClausePosition,
      PositionedPeriodicCNF.canonicalLiteralPosition,
      composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      PeriodicVariablePlacement.translation,
      composedGadgetScale, PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      literalAtom, literalOffset,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring
  simpa [composedGadgetScale, PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale, centerEq] using translated

/-- The ordered finite connector costs at most 73 additional cells beyond
the scaled source-route radius. -/
theorem fanInheritedRouteSuffix_point_withinCanonicalLiteralRadius
    {Variable : Type*} [DecidableEq Variable]
    {radius : Nat}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceLiteral : PeriodicLiteral Variable)
    (generatedLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (data : ComposedClauseExitFanData)
    (slot : Fin 3)
    (sourceRoute : List Cell)
    (fanValid : data.IsValid)
    (slotActive : data.SlotActive slot)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause))
    (sourceBounds :
      ∀ sourcePoint ∈ sourceRoute,
        WithinCoordinateRadius radius
          (PositionedPeriodicCNF.canonicalLiteralPosition
            sourcePlacement sourceClause sourceLiteral)
          sourcePoint)
    (literalAtom :
      generatedLiteral.atom = .inl (.inl sourceLiteral.atom))
    (literalOffset :
      generatedLiteral.offset = sourceLiteral.offset)
    {point : Cell}
    (pointMember :
      point ∈
        fanInheritedRouteSuffix
          (composedPlacement source sourcePlacement)
          sourcePlacement sourceClause generatedClause
          data slot sourceRoute) :
    WithinCoordinateRadius (72 * radius + 73)
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (composedPlacement source sourcePlacement)
        generatedClause generatedLiteral)
      point := by
  let outputPlacement := composedPlacement source sourcePlacement
  let origin :=
    normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute
  let connector := data.translatedRoute origin slot
  change point ∈ replacePolylineHead connector transformed at pointMember
  unfold replacePolylineHead at pointMember
  rcases mem_joinAtEndpoint pointMember with
    connectorMember | transformedTailMember
  · have transformedHead : transformed.head? = some origin := by
      simpa [transformed, origin, outputPlacement] using
        inheritedSourceRoute_head?
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceRoute sourceHead
    have originMember : origin ∈ transformed :=
      List.mem_of_mem_head? transformedHead
    have originBounded :=
      inheritedSourceRoute_point_withinCanonicalLiteralRadius
        source sourcePlacement sourceClause generatedClause
        sourceLiteral generatedLiteral sourceRoute sourceBounds
        literalAtom literalOffset originMember
    have connectorBounded :=
      data.translatedRoute_points_within_sourceNeighborhood
        origin fanValid slot slotActive connectorMember
    exact originBounded.trans connectorBounded
  · have transformedMember : point ∈ transformed :=
      List.mem_of_mem_tail transformedTailMember
    have bounded :=
      inheritedSourceRoute_point_withinCanonicalLiteralRadius
        source sourcePlacement sourceClause generatedClause
        sourceLiteral generatedLiteral sourceRoute sourceBounds
        literalAtom literalOffset transformedMember
    exact bounded.mono (Nat.le_add_right _ _)

/-- Every genuine ordered inherited suffix has the scaled source radius plus
the radius-73 finite connector. -/
theorem orderedInheritedRouteSuffixesRoutes_point_withinCanonicalLiteralRadius
    {Variable : Type*} [DecidableEq Variable]
    {radius : Nat}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceFanValid :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        sourceClause.literals ≠ [] →
        (PositionedPeriodicCNF.clauseExitFanData
          sourceClause sourceClauseIndex sourceRoutes).IsValid)
    (sourceHead :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).head? =
            some
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause))
    (sourceBounds :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∀ sourcePoint ∈
              sourceRoutes sourceClauseIndex sourceLiteralIndex,
            WithinCoordinateRadius radius
              (PositionedPeriodicCNF.canonicalLiteralPosition
                sourcePlacement sourceClause sourceLiteral)
              sourcePoint)
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource :
      literal.atom = .inl (.inl sourceAtom))
    {point : Cell}
    (pointMember :
      point ∈
        orderedInheritedRouteSuffixesRoutes
          source sourcePlacement sourceWidth sourceRoutes
          clauseIndex literalIndex) :
    WithinCoordinateRadius (72 * radius + 73)
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (composedPlacement source sourcePlacement)
        clause literal)
      point := by
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  have generatedClauseEqual : data.generatedClause = clause :=
    (List.mem_zipIdx' data.generatedClauseMember).2.trans
      (List.mem_zipIdx' clauseMember).2.symm
  subst clause
  have generatedLiteralEqual : data.generatedLiteral = literal :=
    (List.mem_zipIdx' data.generatedLiteralMember).2.trans
      (List.mem_zipIdx' literalMember).2.symm
  subst literal
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex sourceRoutes
  let slot := data.sourceSlot sourceWidth
  have sourceIndexLt := data.sourceLiteralIndex_lt
  have sourceClauseWidth := data.sourceClause_width sourceWidth
  have sourceClausePositive : 0 < data.sourceClause.literals.length := by
    omega
  have fanCount : fanData.count = data.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      data.sourceClause data.sourceClauseIndex sourceRoutes
      sourceClausePositive sourceClauseWidth
  have slotActive : fanData.SlotActive slot := by
    unfold ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    exact sourceIndexLt
  rw [
    orderedInheritedRouteSuffixesRoutes_eq_fanInheritedRouteSuffix_of_lookup
      source sourcePlacement sourceWidth sourceRoutes
      clauseIndex literalIndex data dataLookup] at pointMember
  exact
    fanInheritedRouteSuffix_point_withinCanonicalLiteralRadius
      source sourcePlacement data.sourceClause data.generatedClause
      data.sourceLiteral data.generatedLiteral fanData slot
      (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
      (sourceFanValid
        data.sourceClause data.sourceClauseIndex data.sourceClauseMember
        (List.length_pos_iff.mp sourceClausePositive))
      slotActive
      (sourceHead
        data.sourceClause data.sourceClauseIndex data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex data.sourceLiteralMember)
      (sourceBounds
        data.sourceClause data.sourceClauseIndex data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex data.sourceLiteralMember)
      data.literalAtom data.literalOffset pointMember

/-- A final incidence whose atom is not inherited from the original source
has a singleton suffix.  Its normalized local route is therefore within
radius 144 of its final variable endpoint: both it and that endpoint lie in
the same radius-72 source-gauge square. -/
theorem normalizedLocalRoutes_point_withinCanonicalLiteralRadius_of_auxiliary
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (literalAuxiliary :
      ¬ ∃ sourceAtom, literal.atom = .inl (.inl sourceAtom))
    {point : Cell}
    (pointMember :
      point ∈ normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex) :
    WithinCoordinateRadius 144
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (composedPlacement source sourcePlacement)
        clause literal)
      point := by
  let suffixes :=
    completeRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct original
  have suffixSingleton :
      suffixes.routes clauseIndex literalIndex =
        [normalizedLocalEndpoint
          source sourcePlacement clauseIndex literalIndex] := by
    have shape := completeRouteSuffixes_routes_of_members
      source sourcePlacement sourceWidth sourceDistinct original
      clauseMember literalMember
    rcases atomEq : literal.atom with inherited | unitAuxiliary
    · rcases inheritedEq : inherited with sourceAtom | figureAuxiliary
      · exfalso
        exact literalAuxiliary
          ⟨sourceAtom, by simp [atomEq, inheritedEq]⟩
      · simpa [suffixes, atomEq, inheritedEq] using shape
    · simpa [suffixes, atomEq] using shape
  have suffixEndpoints :=
    suffixes.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
  have endpointEq :
      normalizedLocalEndpoint
          source sourcePlacement clauseIndex literalIndex =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (composedPlacement source sourcePlacement)
          clause literal := by
    rw [suffixSingleton] at suffixEndpoints
    simpa using suffixEndpoints.2
  rcases normalizedLocalRoutes_points_within_sourceGaugeRadius72_of_members
      source sourcePlacement sourceWidth clauseMember literalMember with
    ⟨metadata, metadataLookup, metadataClause,
      sourceClauseMember, localBounds⟩
  have localEndpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  have endpointMember :
      normalizedLocalEndpoint
          source sourcePlacement clauseIndex literalIndex ∈
        normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex :=
    mem_of_getLast?_eq_some localEndpoints.2
  have endpointBounded := localBounds _ endpointMember
  have pointBounded := localBounds point pointMember
  have bounded := endpointBounded.symm.trans pointBounded
  rw [endpointEq] at bounded
  simpa using bounded

/-- For an original-source variable, a local composed route costs at most 72
cells beyond the scaled distance from the source literal to its clause
vertex. -/
theorem normalizedLocalRoutes_point_withinCanonicalLiteralRadius_of_source
    {Variable : Type*} [DecidableEq Variable]
    {radius : Nat}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceHead :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).head? =
            some
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause))
    (sourceBounds :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∀ sourcePoint ∈
              sourceRoutes sourceClauseIndex sourceLiteralIndex,
            WithinCoordinateRadius radius
              (PositionedPeriodicCNF.canonicalLiteralPosition
                sourcePlacement sourceClause sourceLiteral)
              sourcePoint)
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource :
      literal.atom = .inl (.inl sourceAtom))
    {point : Cell}
    (pointMember :
      point ∈ normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex) :
    WithinCoordinateRadius (72 * radius + 72)
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (composedPlacement source sourcePlacement)
        clause literal)
      point := by
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  have generatedClauseEqual : data.generatedClause = clause :=
    (List.mem_zipIdx' data.generatedClauseMember).2.trans
      (List.mem_zipIdx' clauseMember).2.symm
  subst clause
  have generatedLiteralEqual : data.generatedLiteral = literal :=
    (List.mem_zipIdx' data.generatedLiteralMember).2.trans
      (List.mem_zipIdx' literalMember).2.symm
  subst literal
  rcases normalizedLocalRoutes_points_within_sourceGaugeRadius72_of_members
      source sourcePlacement sourceWidth
      data.generatedClauseMember data.generatedLiteralMember with
    ⟨metadata, metadataLookup, metadataClause,
      metadataSourceClauseMember, localBounds⟩
  have metadataEqual : metadata = data.metadata :=
    Option.some.inj (metadataLookup.symm.trans data.metadataLookup)
  subst metadata
  rw [data.metadataSourceClause] at localBounds
  let outputPlacement := composedPlacement source sourcePlacement
  let origin :=
    normalizedSourceClausePosition
      outputPlacement data.sourceClause data.generatedClause
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement data.sourceClause
      data.generatedClause
      (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
  have transformedHead : transformed.head? = some origin := by
    simpa [transformed, origin, outputPlacement] using
      inheritedSourceRoute_head?
        outputPlacement sourcePlacement data.sourceClause
        data.generatedClause
        (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
        (sourceHead
          data.sourceClause data.sourceClauseIndex data.sourceClauseMember
          data.sourceLiteral data.sourceLiteralIndex data.sourceLiteralMember)
  have originMember : origin ∈ transformed :=
    List.mem_of_mem_head? transformedHead
  have originBounded :=
    inheritedSourceRoute_point_withinCanonicalLiteralRadius
      source sourcePlacement data.sourceClause data.generatedClause
      data.sourceLiteral data.generatedLiteral
      (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
      (sourceBounds
        data.sourceClause data.sourceClauseIndex data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex data.sourceLiteralMember)
      data.literalAtom data.literalOffset originMember
  have pointBounded :
      WithinCoordinateRadius 72 origin point := by
    change
      WithinCoordinateRadius 72
        (normalizedSourceClausePosition
          (composedPlacement source sourcePlacement)
          data.sourceClause data.generatedClause)
        point
    rw [normalizedSourceClausePosition_eq_scale_sourceGaugeCenter]
    exact localBounds point pointMember
  exact originBounded.trans pointBounded

/-- Combining the local route with the completed suffix gives a uniform
`72 * radius + 144` bound for every composed Figure 9 incidence. -/
theorem splicedRoutes_point_withinCanonicalLiteralRadius
    {Variable : Type*} [DecidableEq Variable]
    {radius : Nat}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceFanValid :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        sourceClause.literals ≠ [] →
        (PositionedPeriodicCNF.clauseExitFanData
          sourceClause sourceClauseIndex sourceRoutes).IsValid)
    (sourceHead :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).head? =
            some
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause))
    (sourceBounds :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∀ sourcePoint ∈
              sourceRoutes sourceClauseIndex sourceLiteralIndex,
            WithinCoordinateRadius radius
              (PositionedPeriodicCNF.canonicalLiteralPosition
                sourcePlacement sourceClause sourceLiteral)
              sourcePoint)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    (originalRoutes :
      original.routes =
        orderedInheritedRouteSuffixesRoutes
          source sourcePlacement sourceWidth sourceRoutes)
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        splicedRoutes
          source sourcePlacement sourceWidth sourceDistinct original
          clauseIndex literalIndex) :
    WithinCoordinateRadius (72 * radius + 144)
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (composedPlacement source sourcePlacement)
        clause literal)
      point := by
  let suffixes :=
    completeRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct original
  change
    point ∈
      PositionedPeriodicCNF.spliceLocalIncidenceRoutes
        (normalizedLocalRoutes source sourcePlacement)
        suffixes clauseIndex literalIndex at pointMember
  unfold PositionedPeriodicCNF.spliceLocalIncidenceRoutes at pointMember
  rcases mem_joinAtEndpoint pointMember with localMember | suffixMember
  · by_cases literalInherited :
        ∃ sourceAtom, literal.atom = .inl (.inl sourceAtom)
    · rcases literalInherited with ⟨sourceAtom, literalSource⟩
      have bounded :=
        normalizedLocalRoutes_point_withinCanonicalLiteralRadius_of_source
          source sourcePlacement sourceWidth sourceDistinct sourceRoutes
          sourceHead sourceBounds clauseMember literalMember
          sourceAtom literalSource localMember
      exact bounded.mono (by omega)
    · have bounded :=
        normalizedLocalRoutes_point_withinCanonicalLiteralRadius_of_auxiliary
          source sourcePlacement sourceWidth sourceDistinct original
          clauseMember literalMember literalInherited localMember
      exact bounded.mono (by omega)
  · by_cases literalInherited :
        ∃ sourceAtom, literal.atom = .inl (.inl sourceAtom)
    · rcases literalInherited with ⟨sourceAtom, literalSource⟩
      have suffixShape := completeRouteSuffixes_routes_of_members
        source sourcePlacement sourceWidth sourceDistinct original
        clauseMember literalMember
      have suffixEq :
          suffixes.routes clauseIndex literalIndex =
            original.routes clauseIndex literalIndex := by
        simpa [suffixes, literalSource] using suffixShape
      rw [suffixEq, originalRoutes] at suffixMember
      have bounded :=
        orderedInheritedRouteSuffixesRoutes_point_withinCanonicalLiteralRadius
          source sourcePlacement sourceWidth sourceDistinct sourceRoutes
          sourceFanValid sourceHead sourceBounds
          clauseMember literalMember sourceAtom literalSource suffixMember
      exact bounded.mono (by omega)
    · have suffixShape := completeRouteSuffixes_routes_of_members
        source sourcePlacement sourceWidth sourceDistinct original
        clauseMember literalMember
      have suffixSingleton :
          suffixes.routes clauseIndex literalIndex =
            [normalizedLocalEndpoint
              source sourcePlacement clauseIndex literalIndex] := by
        rcases atomEq : literal.atom with inherited | unitAuxiliary
        · rcases inheritedEq : inherited with sourceAtom | figureAuxiliary
          · exfalso
            exact literalInherited
              ⟨sourceAtom, by simp [atomEq, inheritedEq]⟩
          · simpa [suffixes, atomEq, inheritedEq] using suffixShape
        · simpa [suffixes, atomEq] using suffixShape
      have suffixEndpoints :=
        suffixes.endpoints clause clauseIndex clauseMember
          literal literalIndex literalMember
      have endpointEq :
          normalizedLocalEndpoint
              source sourcePlacement clauseIndex literalIndex =
            PositionedPeriodicCNF.canonicalLiteralPosition
              (composedPlacement source sourcePlacement)
              clause literal := by
        rw [suffixSingleton] at suffixEndpoints
        simpa using suffixEndpoints.2
      rw [suffixSingleton] at suffixMember
      simp only [List.mem_singleton] at suffixMember
      subst point
      rw [endpointEq]
      exact withinCoordinateRadius_refl _ _

end PlanarOneInThreeNoUnitsFigureNine

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 4000000

/-- Every raw point of the ordered composed Figure 9 route family lies
within one output period of its canonical literal endpoint. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPeriod
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) :
    WithinCoordinateRadius
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).period
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source)
        clause literal)
      point := by
  let sourceFormula := retainedFigureNineClearancePositionedFormula source
  let sourcePlacement := retainedFigureNineClearancePlacement source
  let sourceRoutes := retainedFigureNineClearanceIncidenceRoutes source
  let clearanceRadius :=
    retainedFigureNineSourceClearanceFactor *
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        source).period - 1)
  let finalWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let finalDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let original :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have sourceRadiusBounds :
      PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariableRadius
        clearanceRadius sourceFormula sourcePlacement sourceRoutes := by
    simpa [clearanceRadius, sourceFormula, sourcePlacement, sourceRoutes] using
      retainedFigureNineClearanceIncidenceRoutes_withinVariableClearanceRadius
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  have sourceRawBounds :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ sourceFormula.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∀ sourcePoint ∈
              sourceRoutes sourceClauseIndex sourceLiteralIndex,
            WithinCoordinateRadius clearanceRadius
              (PositionedPeriodicCNF.canonicalLiteralPosition
                sourcePlacement sourceClause sourceLiteral)
              sourcePoint := by
    intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
      sourcePoint sourcePointMember
    exact
      PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariableRadius.rawRoutePointsWithinCanonicalLiteralRadius
        sourceRadiusBounds sourceClauseMember sourceLiteralMember
        sourcePointMember
  have originalRoutes :
      original.routes =
        PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes
          sourceFormula sourcePlacement finalWidth sourceRoutes := by
    rfl
  have commonBound :=
    PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_point_withinCanonicalLiteralRadius
      sourceFormula sourcePlacement finalWidth finalDistinct sourceRoutes
      (fun sourceClause sourceClauseIndex sourceClauseMember
          sourceClauseNonempty =>
        retainedFigureNineClearance_clauseExitFanData_valid
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceClauseNonempty)
      (fun sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember =>
        (retainedFigureNineClearanceIncidenceRoutes_valid
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember).1)
      sourceRawBounds original originalRoutes clauseMember literalMember
      (by
        simpa [sourceFormula, sourcePlacement, sourceRoutes,
          finalWidth, finalDistinct, original,
          retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes]
          using pointMember)
  have basePeriodPositive :
      0 <
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).period :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_pos
      source
  have radiusLe :
      72 * clearanceRadius + 144 ≤
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).period := by
    simp [clearanceRadius,
      retainedFigureNineSourceClearanceFactor_eq,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      retainedFigureNineClearancePlacement,
      PeriodicVariablePlacement.scale_period,
      PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale]
    omega
  exact commonBound.mono radiusLe

/-- The complete ordered composed Figure 9 family has the rebased
one-period variable-radius certificate. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    PositionedPeriodicCNF.rebasedIncidenceRoutesWithinVariableRadius_of_rawRoutePointsWithinCanonicalLiteralRadius
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember point pointMember
  exact
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPeriod
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember pointMember

/-- Final orthogonal normalization preserves the complete composed
one-period variable-radius certificate. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  have rawBounds :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_withinVariablePeriod
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have normalizedBounds :=
    rawBounds.normalizeOrthogonalIncidenceRoutes
      (by
        intro clause clauseIndex clauseMember
          literal literalIndex literalMember
        have valid :=
          retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember
        intro routeEmpty
        rw [routeEmpty] at valid
        simp at valid)
      (by
        intro clause clauseIndex clauseMember
          literal literalIndex literalMember
        exact
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember).2.2)
  simpa [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_eq_normalize]
    using normalizedBounds

end PeriodicOrthocrossing
end LeanTrominoes
