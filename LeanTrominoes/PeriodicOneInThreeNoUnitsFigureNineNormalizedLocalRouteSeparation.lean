/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRouteBounds
import LeanTrominoes.PositionedPeriodicCNFNormalizedRouteSeparation

/-!
# Relative separation of normalized composed local routes

The selected Figure 9-plus-unit-elimination routes are first described in
displayed physical coordinates and then shifted into each final clause's
canonical anchor gauge.  The generic two-anchor calculation specializes here
to move ordinary and strict physical separation into the stored local route
family used by the complete splice.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A physical separation certificate at the anchor-adjusted relative offset
gives separation of the corresponding normalized local routes. -/
theorem normalizedLocalRoutes_relative_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (firstLiteralIndex secondLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (physicalAvoid :
      RoutesAvoidEachOther
        (localRoutes source firstClauseIndex firstLiteralIndex)
        ((localRoutes source
            secondClauseIndex secondLiteralIndex).map
          (Cell.add
            (PositionedPeriodicCNF.relativePhysicalRouteOffset
              (composedPlacement source sourcePlacement)
              firstClause secondClause relativeTranslate)))) :
    RoutesAvoidEachOther
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      ((normalizedLocalRoutes source sourcePlacement
          secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((composedPlacement source sourcePlacement).translation
            relativeTranslate))) := by
  rcases formulaClauseMetadata_lookup source firstClauseMember with
    ⟨firstMetadata, firstLookup, firstClauseEqual⟩
  rcases formulaClauseMetadata_lookup source secondClauseMember with
    ⟨secondMetadata, secondLookup, secondClauseEqual⟩
  subst firstClause
  subst secondClause
  simpa [normalizedLocalRoutes, firstLookup, secondLookup] using
    PositionedPeriodicCNF.normalizeIncidenceRoutes_relative_avoidEachOther
      (composedPlacement source sourcePlacement)
      firstMetadata.clause secondMetadata.clause
      (localRoutes source firstClauseIndex firstLiteralIndex)
      (localRoutes source secondClauseIndex secondLiteralIndex)
      relativeTranslate physicalAvoid

/-- The same anchor-adjusted transport preserves contact-free separation. -/
theorem normalizedLocalRoutes_relative_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (firstLiteralIndex secondLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (physicalAvoid :
      RoutesStrictlyAvoidEachOther
        (localRoutes source firstClauseIndex firstLiteralIndex)
        ((localRoutes source
            secondClauseIndex secondLiteralIndex).map
          (Cell.add
            (PositionedPeriodicCNF.relativePhysicalRouteOffset
              (composedPlacement source sourcePlacement)
              firstClause secondClause relativeTranslate)))) :
    RoutesStrictlyAvoidEachOther
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      ((normalizedLocalRoutes source sourcePlacement
          secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((composedPlacement source sourcePlacement).translation
            relativeTranslate))) := by
  rcases formulaClauseMetadata_lookup source firstClauseMember with
    ⟨firstMetadata, firstLookup, firstClauseEqual⟩
  rcases formulaClauseMetadata_lookup source secondClauseMember with
    ⟨secondMetadata, secondLookup, secondClauseEqual⟩
  subst firstClause
  subst secondClause
  simpa [normalizedLocalRoutes, firstLookup, secondLookup] using
    PositionedPeriodicCNF.normalizeIncidenceRoutes_relative_strictlyAvoidEachOther
      (composedPlacement source sourcePlacement)
      firstMetadata.clause secondMetadata.clause
      (localRoutes source firstClauseIndex firstLiteralIndex)
      (localRoutes source secondClauseIndex secondLiteralIndex)
      relativeTranslate physicalAvoid

/-- If two relatively positioned local routes come from the same original
source clause and their source-gauge centers agree, the relative clause
anchors cancel exactly.  Thus the comparison reduces to two distinct
incidences in one certified finite Figure 9 drawing. -/
theorem normalizedLocalRoutes_relative_avoidEachOther_of_sameSourceGaugeCenter
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourcePeriodPositive : 0 < sourcePlacement.period)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
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
    (relativeTranslate : Cell)
    (centersEqual :
      localRouteSourceGaugeCenter sourcePlacement
          firstMetadata.sourceClause firstClause =
        Cell.add (sourcePlacement.translation relativeTranslate)
          (localRouteSourceGaugeCenter sourcePlacement
            secondMetadata.sourceClause secondClause))
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    RoutesAvoidEachOther
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      ((normalizedLocalRoutes source sourcePlacement
          secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((composedPlacement source sourcePlacement).translation
            relativeTranslate))) := by
  have firstMetadataMember :
      firstMetadata ∈ formulaClauseMetadata source := by
    rcases List.getElem?_eq_some_iff.mp firstLookup with
      ⟨firstIndexLt, firstAt⟩
    rw [← firstAt]
    exact List.getElem_mem firstIndexLt
  have secondMetadataMember :
      secondMetadata ∈ formulaClauseMetadata source := by
    rcases List.getElem?_eq_some_iff.mp secondLookup with
      ⟨secondIndexLt, secondAt⟩
    rw [← secondAt]
    exact List.getElem_mem secondIndexLt
  have sourceClauseEqual :
      firstMetadata.sourceClause = secondMetadata.sourceClause :=
    (formulaClauseMetadata_sourceBlock_eq source
      firstMetadataMember secondMetadataMember sameSource).1
  have incidencesDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex := by
    by_contra incidencesNotDistinct
    simp only [not_or, not_ne_iff] at incidencesNotDistinct
    have clauseEqual : firstClause = secondClause := by
      have secondMemberAtFirst :
          (secondClause, firstClauseIndex) ∈
            (PeriodicOneInThreeNoUnitsPositioned.formula
              (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx := by
        simpa [incidencesNotDistinct.1] using secondClauseMember
      exact
        (List.mem_zipIdx' firstClauseMember).2.trans
          (List.mem_zipIdx' secondMemberAtFirst).2.symm
    have relativeTranslateZero : relativeTranslate = (0, 0) := by
      rw [sourceClauseEqual, clauseEqual] at centersEqual
      rcases relativeTranslate with ⟨translateX, translateY⟩
      have periodPositiveInt : (0 : Int) < sourcePlacement.period := by
        exact_mod_cast sourcePeriodPositive
      apply Prod.ext
      · have coordinateEq := congrArg Prod.fst centersEqual
        simp only [PeriodicVariablePlacement.translation, Cell.add,
          Cell.scale] at coordinateEq
        have productZero :
            (sourcePlacement.period : Int) * translateX = 0 := by
          nlinarith
        exact
          (mul_eq_zero.mp productZero).resolve_left
            (ne_of_gt periodPositiveInt)
      · have coordinateEq := congrArg Prod.snd centersEqual
        simp only [PeriodicVariablePlacement.translation, Cell.add,
          Cell.scale] at coordinateEq
        have productZero :
            (sourcePlacement.period : Int) * translateY = 0 := by
          nlinarith
        exact
          (mul_eq_zero.mp productZero).resolve_left
            (ne_of_gt periodPositiveInt)
    apply generatedOccurrencesDifferent
    apply Prod.ext
    · exact Prod.ext incidencesNotDistinct.1 incidencesNotDistinct.2
    · exact relativeTranslateZero.symm
  have localAvoid :=
    localRoutes_avoidEachOther_of_members_of_same_source
      source sourceWidth sourceDistinct
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstLookup secondLookup sameSource incidencesDistinct
  have physicalOffsetZero :
      PositionedPeriodicCNF.relativePhysicalRouteOffset
          (composedPlacement source sourcePlacement)
          firstClause secondClause relativeTranslate =
        (0, 0) := by
    rw [sourceClauseEqual] at centersEqual
    apply Prod.ext <;>
      norm_num [PositionedPeriodicCNF.relativePhysicalRouteOffset,
        PositionedPeriodicCNF.clauseAnchorTranslation,
        composedPlacement,
        PeriodicOneInThreeNoUnitsPositioned.placement,
        PeriodicOneInThreePositioned.placement,
        PeriodicVariablePlacement.translation,
        localRouteSourceGaugeCenter,
        composedGadgetScale, PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        Cell.add, Cell.sub, Cell.scale]
        at centersEqual ⊢ <;>
      nlinarith
  apply normalizedLocalRoutes_relative_avoidEachOther
    source sourcePlacement firstClauseMember secondClauseMember
      firstLiteralIndex secondLiteralIndex relativeTranslate
  rw [physicalOffsetZero]
  have mapZero :
      (localRoutes source secondClauseIndex secondLiteralIndex).map
          (Cell.add (0, 0)) =
        localRoutes source secondClauseIndex secondLiteralIndex := by
    calc
      _ = (localRoutes source secondClauseIndex secondLiteralIndex).map id := by
        apply List.map_congr_left
        intro point pointMember
        rcases point with ⟨pointX, pointY⟩
        simp [Cell.add]
      _ = _ := List.map_id _
  rw [mapZero]
  exact localAvoid

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
