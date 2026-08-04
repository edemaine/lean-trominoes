import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedRouteSplicing
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteBounds
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteSeparation
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedClausePositionInjectivity
import LeanTrominoes.ScaledPointNeighborhoodSeparation

/-!
# Local-route separation for the ordered retained Figure 9 construction

The extra whole-source factor two turns the tight radius-36 local Figure 9
neighborhoods into neighborhoods of a factor-144 lattice.  Consequently two
local routes are contact-free whenever their unscaled source-gauge centers
are distinct.  This module exposes the remaining equal-center case together
with all source-clause provenance needed to solve it inside one finite
Figure 9 template.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicEightOccurrenceSplit

local instance orderedLocalRouteVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Equality of canonical positions after factor-eight refinement and
clockwise literal ordering descends to a translated equality before both
operations.  The new relative translate accounts for the two anchor gauges
introduced by the reordering. -/
private theorem
    orderedFactorEightCanonicalPosition_eq_translated_imp_exists_unscaled
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (firstBaseClause secondBaseClause :
      PositionedPeriodicClause Variable)
    (firstClauseIndex secondClauseIndex : Nat)
    (firstOrderedClause secondOrderedClause :
      PositionedPeriodicClause Variable)
    (firstOrderedEqual :
      firstOrderedClause =
        PositionedPeriodicCNF.orderClauseByRouteDirection routes
          firstClauseIndex
          (firstBaseClause.scale retainedTerminalFanRoutingRefinement))
    (secondOrderedEqual :
      secondOrderedClause =
        PositionedPeriodicCNF.orderClauseByRouteDirection routes
          secondClauseIndex
          (secondBaseClause.scale retainedTerminalFanRoutingRefinement))
    (relativeTranslate : Cell)
    (positionsEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          (placement.scale retainedTerminalFanRoutingRefinement)
          firstOrderedClause =
        Cell.add
          ((placement.scale
            retainedTerminalFanRoutingRefinement).translation
              relativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement.scale retainedTerminalFanRoutingRefinement)
            secondOrderedClause)) :
    ∃ adjustedTranslate,
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstBaseClause =
        Cell.add (placement.translation adjustedTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            placement secondBaseClause) := by
  let firstBaseAnchor :=
    PeriodicCNF.clauseAnchor firstBaseClause.literals
  let secondBaseAnchor :=
    PeriodicCNF.clauseAnchor secondBaseClause.literals
  let firstOrderedAnchor :=
    PeriodicCNF.clauseAnchor firstOrderedClause.literals
  let secondOrderedAnchor :=
    PeriodicCNF.clauseAnchor secondOrderedClause.literals
  let adjustedTranslate :=
    Cell.add relativeTranslate
      (Cell.sub
        (Cell.sub secondBaseAnchor secondOrderedAnchor)
        (Cell.sub firstBaseAnchor firstOrderedAnchor))
  refine ⟨adjustedTranslate, ?_⟩
  apply Prod.ext
  · have coordinateEqual := congrArg Prod.fst positionsEqual
    simp [firstOrderedEqual, secondOrderedEqual,
      firstBaseAnchor, secondBaseAnchor,
      firstOrderedAnchor, secondOrderedAnchor,
      adjustedTranslate,
      PositionedPeriodicCNF.orderClauseByRouteDirection,
      PositionedPeriodicCNF.canonicalClausePosition,
      PeriodicVariablePlacement.translation,
      retainedTerminalFanRoutingRefinement,
      Cell.add, Cell.sub, Cell.scale] at coordinateEqual ⊢
    nlinarith
  · have coordinateEqual := congrArg Prod.snd positionsEqual
    simp [firstOrderedEqual, secondOrderedEqual,
      firstBaseAnchor, secondBaseAnchor,
      firstOrderedAnchor, secondOrderedAnchor,
      adjustedTranslate,
      PositionedPeriodicCNF.orderClauseByRouteDirection,
      PositionedPeriodicCNF.canonicalClausePosition,
      PeriodicVariablePlacement.translation,
      retainedTerminalFanRoutingRefinement,
      Cell.add, Cell.sub, Cell.scale] at coordinateEqual ⊢
    nlinarith

/-- Canonical clause positions in the final clockwise fixed-eight source
remain injective modulo period translations.  This descends through the
clockwise ordering and factor-eight refinement to the generic positioned
fixed-eight split, whose source macrocells are separated by the retained
planar incidence presentation. -/
theorem
    retainedOrderedFixedEightCanonicalClausePosition_eq_translated_imp_clauseIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            source)
          firstClause =
        Cell.add
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            source).translation relativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              source)
            secondClause)) :
    firstClauseIndex = secondClauseIndex := by
  let baseSource :=
    (finalCoordinatedSource source).scale
      retainedAngularFanSourceClearanceFactor
  let basePlacement :=
    (finalCoordinatedPlacement source).scale
      retainedAngularFanSourceClearanceFactor
  let baseRoutes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes source)
  let occurrencePorts :=
    occurrencePortsOfAngularOrder baseSource.erase
      (PeriodicThreeSATThree.angularOccurrenceOrder
        baseSource.erase baseRoutes)
  let splitFormula :=
    PeriodicEightOccurrenceSplitPositioned.formula
      baseSource basePlacement occurrencePorts
  let splitPlacement :=
    PeriodicEightOccurrenceSplitPositioned.placement basePlacement
  have firstOrderedMember := firstMember
  have secondOrderedMember := secondMember
  rw [retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula]
    at firstOrderedMember secondOrderedMember
  rcases PositionedPeriodicCNF.exists_sourceClause_of_orderedClause_mem
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      firstOrderedMember with
    ⟨firstScaledClause, firstScaledMember, firstOrderedEqual⟩
  rcases PositionedPeriodicCNF.exists_sourceClause_of_orderedClause_mem
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      secondOrderedMember with
    ⟨secondScaledClause, secondScaledMember, secondOrderedEqual⟩
  have firstScaledMember' := firstScaledMember
  have secondScaledMember' := secondScaledMember
  change
    (firstScaledClause, firstClauseIndex) ∈
      (splitFormula.scale
        retainedTerminalFanRoutingRefinement).clauses.zipIdx
    at firstScaledMember'
  change
    (secondScaledClause, secondClauseIndex) ∈
      (splitFormula.scale
        retainedTerminalFanRoutingRefinement).clauses.zipIdx
    at secondScaledMember'
  rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    at firstScaledMember' secondScaledMember'
  rcases List.mem_map.mp firstScaledMember' with
    ⟨firstTaggedClause, firstBaseMember, firstTaggedEqual⟩
  rcases List.mem_map.mp secondScaledMember' with
    ⟨secondTaggedClause, secondBaseMember, secondTaggedEqual⟩
  rcases firstTaggedClause with
    ⟨firstBaseClause, firstBaseClauseIndex⟩
  rcases secondTaggedClause with
    ⟨secondBaseClause, secondBaseClauseIndex⟩
  have firstBaseIndexEqual :
      firstBaseClauseIndex = firstClauseIndex :=
    congrArg Prod.snd firstTaggedEqual
  have secondBaseIndexEqual :
      secondBaseClauseIndex = secondClauseIndex :=
    congrArg Prod.snd secondTaggedEqual
  have firstScaledEqual :
      firstBaseClause.scale retainedTerminalFanRoutingRefinement =
        firstScaledClause :=
    congrArg Prod.fst firstTaggedEqual
  have secondScaledEqual :
      secondBaseClause.scale retainedTerminalFanRoutingRefinement =
        secondScaledClause :=
    congrArg Prod.fst secondTaggedEqual
  subst firstBaseClauseIndex
  subst secondBaseClauseIndex
  subst firstScaledClause
  subst secondScaledClause
  have positionsEqual' :
      PositionedPeriodicCNF.canonicalClausePosition
          (splitPlacement.scale retainedTerminalFanRoutingRefinement)
          firstClause =
        Cell.add
          ((splitPlacement.scale
            retainedTerminalFanRoutingRefinement).translation
              relativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            (splitPlacement.scale retainedTerminalFanRoutingRefinement)
            secondClause) := by
    simpa [splitPlacement, basePlacement,
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
      retainedAngularFanSourceScaledRefinedPlacement,
      retainedAngularFanRefinedPlacement,
      finalCoordinatedPlacement] using positionsEqual
  rcases
      orderedFactorEightCanonicalPosition_eq_translated_imp_exists_unscaled
        splitPlacement
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        firstBaseClause secondBaseClause
        firstClauseIndex secondClauseIndex
        firstClause secondClause
        firstOrderedEqual secondOrderedEqual
        relativeTranslate positionsEqual' with
    ⟨adjustedTranslate, basePositionsEqual⟩
  have graphWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed source
  have graphDegree :=
    PeriodicCNF.incidenceGraph_degreeAtMost
      sourceWidth sourceOccurrences
  have graphLocal :=
    PeriodicCNF.incidenceGraph_isLocal sourceLocal
  have retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source sourceClausesNonempty
  let presentation :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATPlanarIncidencePresentation
      retainedAngularFanSourceClearanceFactor_pos
      source graphWellFormed graphDegree graphLocal
      retainedClausesNonempty
  have presentation' :
      PositionedPeriodicCNF.PlanarIncidencePresentation
        baseSource basePlacement := by
    have wrappedDecidableEqEqual :
        (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
            Variable _ ) =
          (@instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable) _) :=
      Subsingleton.elim _ _
    rw [wrappedDecidableEqEqual]
    simpa [baseSource, basePlacement,
      finalCoordinatedSource, finalCoordinatedPlacement] using
      presentation
  exact
    PeriodicEightOccurrenceSplitPositioned.canonicalClausePosition_eq_translated_imp_clauseIndex_eq
      baseSource basePlacement occurrencePorts presentation'
      firstBaseMember secondBaseMember adjustedTranslate
      (by simpa [splitFormula, splitPlacement]
        using basePositionsEqual)

/-- Equality of source-gauge centers is exactly equality of the two
canonical source-clause representatives at the inherited, anchor-adjusted
source translation. -/
theorem localRouteSourceGaugeCenter_eq_translated_iff
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (firstSourceClause secondSourceClause :
      PositionedPeriodicClause Variable)
    (firstGeneratedClause secondGeneratedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
    (relativeTranslate : Cell) :
    PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
        sourcePlacement firstSourceClause firstGeneratedClause =
      Cell.add (sourcePlacement.translation relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
          sourcePlacement secondSourceClause secondGeneratedClause) ↔
      PositionedPeriodicCNF.canonicalClausePosition
          sourcePlacement firstSourceClause =
        Cell.add
          (sourcePlacement.translation
            (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
              firstSourceClause secondSourceClause
              firstGeneratedClause secondGeneratedClause
              relativeTranslate))
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement secondSourceClause) := by
  constructor
  · intro equal
    apply Prod.ext
    · have coordinateEq := congrArg Prod.fst equal
      simp [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
        PositionedPeriodicCNF.canonicalClausePosition,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.sub, Cell.scale] at coordinateEq ⊢
      nlinarith
    · have coordinateEq := congrArg Prod.snd equal
      simp [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
        PositionedPeriodicCNF.canonicalClausePosition,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.sub, Cell.scale] at coordinateEq ⊢
      nlinarith
  · intro equal
    apply Prod.ext
    · have coordinateEq := congrArg Prod.fst equal
      simp [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
        PositionedPeriodicCNF.canonicalClausePosition,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.sub, Cell.scale] at coordinateEq ⊢
      nlinarith
    · have coordinateEq := congrArg Prod.snd equal
      simp [PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
        PositionedPeriodicCNF.canonicalClausePosition,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.sub, Cell.scale] at coordinateEq ⊢
      nlinarith

/-- For two genuine final incidences, recover their unscaled clockwise
source clauses.  Either the corresponding source-gauge centers coincide, or
the two relatively positioned normalized local routes are contact-free. -/
theorem
    retainedOrderedFixedEightFigureNineNormalizedLocalRoutes_relative_sameSourceGaugeCenter_or_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (retainedFigureNineClearancePositionedFormula source))).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (retainedFigureNineClearancePositionedFormula source))).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell) :
    ∃ firstMetadata secondMetadata
        firstSourceClause secondSourceClause,
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          firstClauseIndex]? = some firstMetadata ∧
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          secondClauseIndex]? = some secondMetadata ∧
      firstMetadata.clause = firstClause ∧
      secondMetadata.clause = secondClause ∧
      (firstSourceClause, firstMetadata.sourceClauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx ∧
      (secondSourceClause, secondMetadata.sourceClauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx ∧
      firstMetadata.sourceClause =
        firstSourceClause.scale retainedFigureNineSourceClearanceFactor ∧
      secondMetadata.sourceClause =
        secondSourceClause.scale retainedFigureNineSourceClearanceFactor ∧
      (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            source)
          firstSourceClause firstClause =
        Cell.add
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            source).translation relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              source)
            secondSourceClause secondClause) ∨
        RoutesStrictlyAvoidEachOther
          (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)
            firstClauseIndex firstLiteralIndex)
          ((PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source)
              secondClauseIndex secondLiteralIndex).map
            (Cell.add
              ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
                (retainedFigureNineClearancePositionedFormula source)
                (retainedFigureNineClearancePlacement source)).translation
                  relativeTranslate)))) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clockwisePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  rcases
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_points_within_sourceGaugeNeighborhood_of_members
        clearanceSource clearancePlacement
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)
        firstClauseMember firstLiteralMember with
    ⟨firstMetadata, firstLookup, firstClauseEq,
      firstClearanceSourceMember, firstBounded⟩
  rcases
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_points_within_sourceGaugeNeighborhood_of_members
        clearanceSource clearancePlacement
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)
        secondClauseMember secondLiteralMember with
    ⟨secondMetadata, secondLookup, secondClauseEq,
      secondClearanceSourceMember, secondBounded⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      firstClearanceSourceMember with
    ⟨firstSourceClause, firstSourceMember, firstSourceEq⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      secondClearanceSourceMember with
    ⟨secondSourceClause, secondSourceMember, secondSourceEq⟩
  refine
    ⟨firstMetadata, secondMetadata,
      firstSourceClause, secondSourceClause,
      firstLookup, secondLookup, firstClauseEq, secondClauseEq,
      firstSourceMember, secondSourceMember,
      firstSourceEq, secondSourceEq, ?_⟩
  let firstCenter :=
    PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
      clockwisePlacement firstSourceClause firstClause
  let secondCenter :=
    Cell.add (clockwisePlacement.translation relativeTranslate)
      (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
        clockwisePlacement secondSourceClause secondClause)
  by_cases centersEqual : firstCenter = secondCenter
  · exact Or.inl centersEqual
  · apply Or.inr
    apply
      routesStrictlyAvoidEachOther_of_distinct_offsetScaledCoordinateNeighborhoods
        (firstCenter := firstCenter)
        (secondCenter := secondCenter)
        (factor := 144)
        (radius := 36)
        (offset :=
          PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset)
        centersEqual
    · native_decide
    · native_decide
    · intro point pointMember
      have bounded := firstBounded point pointMember
      have centerEq :
          Cell.add
              (Cell.scale
                PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
                  clearancePlacement firstMetadata.sourceClause firstClause))
              PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset =
            Cell.add
              (Cell.scale
                144
                firstCenter)
              PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset := by
        rw [firstSourceEq]
        apply Prod.ext <;>
          simp [firstCenter, clockwisePlacement, clearancePlacement,
            retainedFigureNineClearancePlacement,
            PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
            PlanarOneInThree.gadgetScale,
            PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
            PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
            Cell.add, Cell.sub, Cell.scale] <;>
          ring
      rwa [centerEq] at bounded
    · intro point pointMember
      rcases List.mem_map.mp pointMember with
        ⟨sourcePoint, sourcePointMember, rfl⟩
      have bounded :=
        (secondBounded sourcePoint sourcePointMember).translate
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            clearanceSource clearancePlacement).translation
              relativeTranslate)
      have centerEq :
          Cell.add
              ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
                clearanceSource clearancePlacement).translation
                  relativeTranslate)
              (Cell.add
                (Cell.scale
                  PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                  (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
                    clearancePlacement secondMetadata.sourceClause
                    secondClause))
                PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset) =
            Cell.add
              (Cell.scale
                144
                secondCenter)
              PlanarOneInThreeNoUnitsFigureNine.localRouteNeighborhoodOffset := by
        rw [secondSourceEq]
        apply Prod.ext <;>
          simp [secondCenter, clockwisePlacement,
            clearanceSource, clearancePlacement,
            retainedFigureNineClearancePlacement,
            PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
            PeriodicOneInThreeNoUnitsPositioned.placement,
            PeriodicOneInThreePositioned.placement,
            PeriodicVariablePlacement.translation,
            PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
            PlanarOneInThree.gadgetScale,
            PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
            PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
            Cell.add, Cell.sub, Cell.scale] <;>
          ring
      rw [centerEq] at bounded
      simpa [clearanceSource, clearancePlacement] using bounded

/-- Any two distinct relatively positioned generated incidences have
contact-free normalized local Figure 9 routes.  Distinct source-gauge
centers use the global factor-144 clearance; equal centers first reduce, by
fixed-eight clause-position injectivity, to two incidences in one finite
Figure 9 source block. -/
theorem
    retainedOrderedFixedEightFigureNineNormalizedLocalRoutes_relative_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (retainedFigureNineClearancePositionedFormula source))).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (retainedFigureNineClearancePositionedFormula source))).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    RoutesAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
      ((PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate))) := by
  rcases
      retainedOrderedFixedEightFigureNineNormalizedLocalRoutes_relative_sameSourceGaugeCenter_or_strictlyAvoidEachOther
        source sourceWidth firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember relativeTranslate with
    ⟨firstMetadata, secondMetadata,
      firstSourceClause, secondSourceClause,
      firstLookup, secondLookup,
      firstClauseEqual, secondClauseEqual,
      firstSourceMember, secondSourceMember,
      firstSourceEqual, secondSourceEqual,
      centersEqual | strictlyAvoid⟩
  · have sourceCanonicalPositionsEqual :=
      (localRouteSourceGaugeCenter_eq_translated_iff
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source)
        firstSourceClause secondSourceClause
        firstClause secondClause relativeTranslate).mp
          centersEqual
    have sourceClauseIndicesEqual :=
      retainedOrderedFixedEightCanonicalClausePosition_eq_translated_imp_clauseIndex_eq
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstSourceMember secondSourceMember
        (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          firstSourceClause secondSourceClause
          firstClause secondClause relativeTranslate)
        sourceCanonicalPositionsEqual
    have clearanceCentersEqual :
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            (retainedFigureNineClearancePlacement source)
            firstMetadata.sourceClause firstClause =
          Cell.add
            ((retainedFigureNineClearancePlacement source).translation
              relativeTranslate)
            (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
              (retainedFigureNineClearancePlacement source)
              secondMetadata.sourceClause secondClause) := by
      rw [firstSourceEqual, secondSourceEqual]
      apply Prod.ext
      · have coordinateEqual := congrArg Prod.fst centersEqual
        simp [retainedFigureNineClearancePlacement,
          PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
          PeriodicVariablePlacement.translation,
          retainedFigureNineSourceClearanceFactor,
          Cell.add, Cell.sub, Cell.scale] at coordinateEqual ⊢
        nlinarith
      · have coordinateEqual := congrArg Prod.snd centersEqual
        simp [retainedFigureNineClearancePlacement,
          PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
          PeriodicVariablePlacement.translation,
          retainedFigureNineSourceClearanceFactor,
          Cell.add, Cell.sub, Cell.scale] at coordinateEqual ⊢
        nlinarith
    exact
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_relative_avoidEachOther_of_sameSourceGaugeCenter
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        (retainedFigureNineClearancePlacement_period_pos source)
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedFigureNineClearancePositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstLookup secondLookup sourceClauseIndicesEqual
        relativeTranslate clearanceCentersEqual
        generatedOccurrencesDifferent
  · exact strictlyAvoid.toRoutesAvoidEachOther

/-- Equality of a local route's normalized source gauge with a translated
inherited source gauge forces the two recovered retained source clauses to
have the same index.  This is the metadata-facing form of the clockwise
fixed-eight clause-position injectivity theorem. -/
theorem
    retainedOrderedFixedEightFigureNine_sourceClauseIndex_eq_of_normalizedSourceGaugesEqual
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {localClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localClauseIndex : Nat}
    (localClauseMember :
      (localClause, localClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (retainedFigureNineClearancePositionedFormula source))).clauses.zipIdx)
    (localMetadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (localMetadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          localClauseIndex]? = some localMetadata)
    (localMetadataClause : localMetadata.clause = localClause)
    {inheritedClauseIndex inheritedLiteralIndex : Nat}
    (data :
      PlanarOneInThreeNoUnitsFigureNine.InheritedEndpointProvenance
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        inheritedClauseIndex inheritedLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            data.sourceClause data.generatedClause)) :
    localMetadata.sourceClauseIndex = data.sourceClauseIndex := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let clockwisePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  rcases
      PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid_embedded
        clearanceSource localClauseMember with
    ⟨actualMetadata, actualLookup, _actualClause,
      localClearanceSourceMember, _localClauseMember⟩
  have actualMetadataEqual : actualMetadata = localMetadata := by
    apply Option.some.inj
    exact actualLookup.symm.trans localMetadataLookup
  subst actualMetadata
  rcases exists_clockwiseClause_of_clearanceClause_mem
      localClearanceSourceMember with
    ⟨localSourceClause, localSourceMember, localSourceEq⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      data.sourceClauseMember with
    ⟨inheritedSourceClause, inheritedSourceMember,
      inheritedSourceEq⟩
  have clearanceCentersEqual :
      PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
          clearancePlacement localMetadata.sourceClause localClause =
        Cell.add (clearancePlacement.translation relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            clearancePlacement data.sourceClause data.generatedClause) := by
    rw [
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
        clearanceSource clearancePlacement
        localMetadata.sourceClause localClause,
      PlanarOneInThreeNoUnitsFigureNine.translated_normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
        clearanceSource clearancePlacement
        data.sourceClause data.generatedClause relativeTranslate
    ] at sourceGaugesEqual
    exact Cell.scale_injective (by
      norm_num [PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale] :
      PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale ≠ 0)
      sourceGaugesEqual
  have clockwiseCentersEqual :
      PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
          clockwisePlacement localSourceClause localClause =
        Cell.add (clockwisePlacement.translation relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            clockwisePlacement inheritedSourceClause
            data.generatedClause) := by
    rw [localSourceEq, inheritedSourceEq] at clearanceCentersEqual
    apply Prod.ext
    · have coordinateEqual := congrArg Prod.fst clearanceCentersEqual
      simp [clockwisePlacement, clearancePlacement,
        retainedFigureNineClearancePlacement,
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
        PeriodicVariablePlacement.translation,
        retainedFigureNineSourceClearanceFactor,
        Cell.add, Cell.sub, Cell.scale] at coordinateEqual ⊢
      nlinarith
    · have coordinateEqual := congrArg Prod.snd clearanceCentersEqual
      simp [clockwisePlacement, clearancePlacement,
        retainedFigureNineClearancePlacement,
        PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter,
        PeriodicVariablePlacement.translation,
        retainedFigureNineSourceClearanceFactor,
        Cell.add, Cell.sub, Cell.scale] at coordinateEqual ⊢
      nlinarith
  have canonicalPositionsEqual :=
    (localRouteSourceGaugeCenter_eq_translated_iff
      clockwisePlacement localSourceClause inheritedSourceClause
      localClause data.generatedClause relativeTranslate).mp
        clockwiseCentersEqual
  exact
    retainedOrderedFixedEightCanonicalClausePosition_eq_translated_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      localSourceMember inheritedSourceMember
      (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
        localSourceClause inheritedSourceClause
        localClause data.generatedClause relativeTranslate)
      canonicalPositionsEqual

end PeriodicOrthocrossing
end LeanTrominoes
