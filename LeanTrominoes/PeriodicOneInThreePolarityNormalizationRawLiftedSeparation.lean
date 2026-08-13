/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRawRouteDescriptors
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationSplitRouteSeparation

/-!
# Lifted separation of raw polarity-normalized routes

Distinct raw routes either come from distinct lifted refined source routes,
in which case complete source separation passes to endpoint-respecting
fragments, or they are different pieces of one incompatible source route,
in which case the three local split-fragment lemmas apply.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Equal source literals and equal fragment kinds force equal canonical
whole-period shifts. -/
theorem RawRouteShape.latticeShift_eq_of_sourceLiteral_eq_of_fragment_eq
    {Variable : Type*}
    {firstMetadata secondMetadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable}
    {firstLiteral secondLiteral : PeriodicLiteral Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    {firstOutputIndex secondOutputIndex : Nat}
    {firstFragment secondFragment : RawRouteFragment}
    {firstShift secondShift : Cell}
    (firstShape : RawRouteShape firstMetadata firstLiteral
      firstLiteralIndex firstOutputIndex firstFragment firstShift)
    (secondShape : RawRouteShape secondMetadata secondLiteral
      secondLiteralIndex secondOutputIndex secondFragment secondShift)
    (sourceLiteralEq : firstLiteral = secondLiteral)
    (fragmentEq : firstFragment = secondFragment) :
    firstShift = secondShift := by
  cases firstShape <;> cases secondShape <;> simp_all

/-- Different fragments selected from one simple refined source route avoid
one another.  Compatibility rules rule out mixing a whole route with one of
the three incompatible-literal pieces. -/
theorem RawRouteShape.fragmentsAvoid_of_same_source
    {Variable : Type*}
    {firstMetadata secondMetadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable}
    {firstLiteral secondLiteral : PeriodicLiteral Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    {firstOutputIndex secondOutputIndex : Nat}
    {firstFragment secondFragment : RawRouteFragment}
    {firstShift secondShift : Cell}
    (firstShape : RawRouteShape firstMetadata firstLiteral
      firstLiteralIndex firstOutputIndex firstFragment firstShift)
    (secondShape : RawRouteShape secondMetadata secondLiteral
      secondLiteralIndex secondOutputIndex secondFragment secondShift)
    (sourceLiteralEq : firstLiteral = secondLiteral)
    (sourceLiteralIndexEq : firstLiteralIndex = secondLiteralIndex)
    (fragmentsDifferent : firstFragment ≠ secondFragment)
    (route : List Cell)
    (length : 4 ≤ route.length)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    RoutesAvoidEachOther
      (firstFragment.select route) (secondFragment.select route) := by
  cases firstShape with
  | whole _ _ firstCompatible =>
      cases secondShape with
      | whole _ _ _ => exact (fragmentsDifferent rfl).elim
      | «prefix» _ _ secondIncompatible =>
          exact (secondIncompatible
            (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
              firstCompatible)).elim
      | middle _ _ secondIncompatible =>
          exact (secondIncompatible
            (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
              firstCompatible)).elim
      | suffix _ _ secondIncompatible =>
          exact (secondIncompatible
            (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
              firstCompatible)).elim
  | «prefix» _ _ firstIncompatible =>
      cases secondShape with
      | whole _ _ secondCompatible =>
          exact (firstIncompatible
            (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
              secondCompatible)).elim
      | «prefix» _ _ _ => exact (fragmentsDifferent rfl).elim
      | middle _ _ _ =>
          exact prefix_middle_routesAvoidEachOther route length simple
      | suffix _ _ _ =>
          exact prefix_suffix_routesAvoidEachOther route length simple
  | middle _ _ firstIncompatible =>
      cases secondShape with
      | whole _ _ secondCompatible =>
          exact (firstIncompatible
            (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
              secondCompatible)).elim
      | «prefix» _ _ _ =>
          exact routesAvoidEachOther_comm
            (prefix_middle_routesAvoidEachOther route length simple)
      | middle _ _ _ => exact (fragmentsDifferent rfl).elim
      | suffix _ _ _ =>
          exact middle_suffix_routesAvoidEachOther route length simple
  | suffix _ _ firstIncompatible =>
      cases secondShape with
      | whole _ _ secondCompatible =>
          exact (firstIncompatible
            (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
              secondCompatible)).elim
      | «prefix» _ _ _ =>
          exact routesAvoidEachOther_comm
            (prefix_suffix_routesAvoidEachOther route length simple)
      | middle _ _ _ =>
          exact routesAvoidEachOther_comm
            (middle_suffix_routesAvoidEachOther route length simple)
      | suffix _ _ _ => exact (fragmentsDifferent rfl).elim

namespace RawRouteDescriptor

/-- Adding an external route-occurrence translation to a raw descriptor
combines the external shift with the descriptor's canonical source shift. -/
theorem liftedRouteEq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (descriptor : RawRouteDescriptor presentation taggedIncidence)
    (translate : Cell) :
    PeriodicOrthocrossing.translatePolyline
        ((rawIncidenceDrawing presentation).periodTranslation translate)
        (rawIncidenceRoutes source sourcePlacement presentation.routes
          taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex) =
      PeriodicOrthocrossing.translatePolyline
        ((refinedIncidenceDrawing presentation).periodTranslation
          (Cell.add descriptor.latticeShift translate))
        (descriptor.fragment.select
          (refinedRoute presentation.routes
            descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex)) := by
  rw [descriptor.routeEq]
  change PeriodicOrthocrossing.translatePolyline
      ((refinedIncidenceDrawing presentation).periodTranslation translate)
      (PeriodicOrthocrossing.translatePolyline
        ((refinedIncidenceDrawing presentation).periodTranslation
          descriptor.latticeShift)
        (descriptor.fragment.select
          (refinedRoute presentation.routes
            descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex))) = _
  rw [
    PeriodicOrthocrossing.translatePolyline_add,
    PeriodicThreeDM.periodTranslation_add]

end RawRouteDescriptor

/-- The raw split drawing inherits complete avoidance for all distinct
lifted route occurrences. -/
theorem rawIncidenceDrawing_liftedRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps) :
    (rawIncidenceDrawing
      presentation.toContinuousPlanarIncidencePresentation)
        |>.LiftedRoutesAvoidEachOther := by
  let continuous := presentation.toContinuousPlanarIncidencePresentation
  intro first firstMember second secondMember
    firstTranslate secondTranslate occurrencesDifferent
  rcases PositionedPeriodicCNF.exists_incidenceCoordinates_of_taggedRoute
      (rawFormula source sourcePlacement continuous.routes)
      (rawPlacement sourcePlacement continuous.routes)
      (rawIncidenceRoutes source sourcePlacement continuous.routes)
      first firstMember with
    ⟨firstIncidence, firstIncidenceMember, firstClause, firstLiteral,
      firstClauseMember, firstLiteralMember,
      firstRouteEq, firstRouteIndexEq⟩
  rcases PositionedPeriodicCNF.exists_incidenceCoordinates_of_taggedRoute
      (rawFormula source sourcePlacement continuous.routes)
      (rawPlacement sourcePlacement continuous.routes)
      (rawIncidenceRoutes source sourcePlacement continuous.routes)
      second secondMember with
    ⟨secondIncidence, secondIncidenceMember, secondClause, secondLiteral,
      secondClauseMember, secondLiteralMember,
      secondRouteEq, secondRouteIndexEq⟩
  let firstDescriptor :=
    (exists_rawRouteDescriptor continuous firstIncidenceMember).some
  let secondDescriptor :=
    (exists_rawRouteDescriptor continuous secondIncidenceMember).some
  let firstCombinedShift :=
    Cell.add firstDescriptor.latticeShift firstTranslate
  let secondCombinedShift :=
    Cell.add secondDescriptor.latticeShift secondTranslate
  have firstLiftedEq :
      first.1.map
          (Cell.add
            ((rawIncidenceDrawing continuous).periodTranslation
              firstTranslate)) =
        PeriodicOrthocrossing.translatePolyline
          ((refinedIncidenceDrawing continuous).periodTranslation
            firstCombinedShift)
          (firstDescriptor.fragment.select
            (refinedRoute continuous.routes
              firstDescriptor.metadata.sourceClauseIndex
              firstDescriptor.sourceLiteralIndex)) := by
    rw [firstRouteEq]
    exact firstDescriptor.liftedRouteEq firstTranslate
  have secondLiftedEq :
      second.1.map
          (Cell.add
            ((rawIncidenceDrawing continuous).periodTranslation
              secondTranslate)) =
        PeriodicOrthocrossing.translatePolyline
          ((refinedIncidenceDrawing continuous).periodTranslation
            secondCombinedShift)
          (secondDescriptor.fragment.select
            (refinedRoute continuous.routes
              secondDescriptor.metadata.sourceClauseIndex
              secondDescriptor.sourceLiteralIndex)) := by
    rw [secondRouteEq]
    exact secondDescriptor.liftedRouteEq secondTranslate
  by_cases sourceOccurrencesDifferent :
      (firstDescriptor.sourceRouteIndex, firstCombinedShift) ≠
        (secondDescriptor.sourceRouteIndex, secondCombinedShift)
  · have sourceAvoid :=
      refinedRouteFamily_liftedRoutesAvoidEachOther
        presentation sourceUnitSteps
        (refinedRoute continuous.routes
          firstDescriptor.metadata.sourceClauseIndex
          firstDescriptor.sourceLiteralIndex,
          firstDescriptor.sourceRouteIndex)
        firstDescriptor.sourceTaggedRouteMember
        (refinedRoute continuous.routes
          secondDescriptor.metadata.sourceClauseIndex
          secondDescriptor.sourceLiteralIndex,
          secondDescriptor.sourceRouteIndex)
        secondDescriptor.sourceTaggedRouteMember
        firstCombinedShift secondCombinedShift sourceOccurrencesDifferent
    have firstSourceSimple :=
      refinedRouteFamily_routesSimple presentation
        (refinedRoute continuous.routes
          firstDescriptor.metadata.sourceClauseIndex
          firstDescriptor.sourceLiteralIndex)
        (List.fst_mem_of_mem_zipIdx
          firstDescriptor.sourceTaggedRouteMember)
    have secondSourceSimple :=
      refinedRouteFamily_routesSimple presentation
        (refinedRoute continuous.routes
          secondDescriptor.metadata.sourceClauseIndex
          secondDescriptor.sourceLiteralIndex)
        (List.fst_mem_of_mem_zipIdx
          secondDescriptor.sourceTaggedRouteMember)
    have firstSubroute :=
      (RawRouteFragment.endpointSubroute firstDescriptor.fragment
        (refinedRoute continuous.routes
          firstDescriptor.metadata.sourceClauseIndex
          firstDescriptor.sourceLiteralIndex)
        firstDescriptor.sourceRoute_length_ge_four
        firstSourceSimple.1).translate
          ((refinedIncidenceDrawing continuous).periodTranslation
            firstCombinedShift)
    have secondSubroute :=
      (RawRouteFragment.endpointSubroute secondDescriptor.fragment
        (refinedRoute continuous.routes
          secondDescriptor.metadata.sourceClauseIndex
          secondDescriptor.sourceLiteralIndex)
        secondDescriptor.sourceRoute_length_ge_four
        secondSourceSimple.1).translate
          ((refinedIncidenceDrawing continuous).periodTranslation
            secondCombinedShift)
    rw [firstLiftedEq, secondLiftedEq]
    exact sourceAvoid.endpointSubroutes firstSubroute secondSubroute
  · have sourceOccurrencesEqual := Decidable.not_not.mp
      sourceOccurrencesDifferent
    have sourceRouteIndexEq :
        firstDescriptor.sourceRouteIndex =
          secondDescriptor.sourceRouteIndex :=
      congrArg Prod.fst sourceOccurrencesEqual
    have combinedShiftEq : firstCombinedShift = secondCombinedShift :=
      congrArg Prod.snd sourceOccurrencesEqual
    by_cases fragmentEq :
        firstDescriptor.fragment = secondDescriptor.fragment
    · have taggedIncidenceEq :=
        taggedIncidence_eq_of_descriptors_sourceRouteIndex_fragment_eq
          continuous firstIncidenceMember secondIncidenceMember
          firstDescriptor secondDescriptor sourceRouteIndexEq fragmentEq
      have sourceTaggedEq :=
        PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
          firstDescriptor.sourceTaggedIncidenceMember
          secondDescriptor.sourceTaggedIncidenceMember sourceRouteIndexEq
      have sourceLiteralEq :
          firstDescriptor.sourceLiteral = secondDescriptor.sourceLiteral :=
        congrArg CNFIncidence.literal (congrArg Prod.fst sourceTaggedEq)
      have latticeShiftEq :
          firstDescriptor.latticeShift = secondDescriptor.latticeShift :=
        RawRouteShape.latticeShift_eq_of_sourceLiteral_eq_of_fragment_eq
          firstDescriptor.shape secondDescriptor.shape
          sourceLiteralEq fragmentEq
      have translateEq : firstTranslate = secondTranslate := by
        change Cell.add firstDescriptor.latticeShift firstTranslate =
          Cell.add secondDescriptor.latticeShift secondTranslate
            at combinedShiftEq
        rw [latticeShiftEq] at combinedShiftEq
        exact Cell.add_left_injective
          secondDescriptor.latticeShift combinedShiftEq
      exfalso
      apply occurrencesDifferent
      apply Prod.ext
      · exact firstRouteIndexEq.symm.trans
          ((congrArg Prod.snd taggedIncidenceEq).trans
            secondRouteIndexEq)
      · exact translateEq
    · have sourceTaggedEq :=
        PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
          firstDescriptor.sourceTaggedIncidenceMember
          secondDescriptor.sourceTaggedIncidenceMember sourceRouteIndexEq
      have sourceIncidenceEq :
          firstDescriptor.sourceIncidence =
            secondDescriptor.sourceIncidence :=
        congrArg Prod.fst sourceTaggedEq
      have sourceLiteralEq :
          firstDescriptor.sourceLiteral = secondDescriptor.sourceLiteral :=
        congrArg CNFIncidence.literal sourceIncidenceEq
      have sourceLiteralIndexEq :
          firstDescriptor.sourceLiteralIndex =
            secondDescriptor.sourceLiteralIndex :=
        congrArg CNFIncidence.literalIndex sourceIncidenceEq
      have sourceRouteTaggedEq :=
        PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
          firstDescriptor.sourceTaggedRouteMember
          secondDescriptor.sourceTaggedRouteMember sourceRouteIndexEq
      have sourceRouteEq :
          refinedRoute continuous.routes
              firstDescriptor.metadata.sourceClauseIndex
              firstDescriptor.sourceLiteralIndex =
            refinedRoute continuous.routes
              secondDescriptor.metadata.sourceClauseIndex
              secondDescriptor.sourceLiteralIndex :=
        congrArg Prod.fst sourceRouteTaggedEq
      have sourceSimple :=
        refinedRouteFamily_routesSimple presentation
          (refinedRoute continuous.routes
            firstDescriptor.metadata.sourceClauseIndex
            firstDescriptor.sourceLiteralIndex)
          (List.fst_mem_of_mem_zipIdx
            firstDescriptor.sourceTaggedRouteMember)
      have localAvoid := RawRouteShape.fragmentsAvoid_of_same_source
        firstDescriptor.shape secondDescriptor.shape
        sourceLiteralEq sourceLiteralIndexEq fragmentEq
        (refinedRoute continuous.routes
          firstDescriptor.metadata.sourceClauseIndex
          firstDescriptor.sourceLiteralIndex)
        firstDescriptor.sourceRoute_length_ge_four sourceSimple
      have translatedAvoid := routesAvoidEachOther_translate localAvoid
        ((refinedIncidenceDrawing continuous).periodTranslation
          firstCombinedShift)
      rw [firstLiftedEq, secondLiftedEq, ← combinedShiftEq,
        ← sourceRouteEq]
      exact translatedAvoid

/-- Every route of the raw split drawing is simple. -/
theorem rawIncidenceDrawing_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement) :
    ∀ route ∈
        (rawIncidenceDrawing
          presentation.toContinuousPlanarIncidencePresentation).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  let continuous := presentation.toContinuousPlanarIncidencePresentation
  intro route routeMember
  rcases List.mem_iff_get.mp routeMember with
    ⟨routeIndex, routeAt⟩
  let taggedRoute : List Cell × Nat := (route, routeIndex)
  have taggedRouteMember : taggedRoute ∈
      (rawIncidenceDrawing continuous).edgeRoutes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨routeIndex.isLt, routeAt⟩
  rcases PositionedPeriodicCNF.exists_incidenceCoordinates_of_taggedRoute
      (rawFormula source sourcePlacement continuous.routes)
      (rawPlacement sourcePlacement continuous.routes)
      (rawIncidenceRoutes source sourcePlacement continuous.routes)
      taggedRoute taggedRouteMember with
    ⟨taggedIncidence, taggedIncidenceMember, outputClause, outputLiteral,
      outputClauseMember, outputLiteralMember, routeEq, routeIndexEq⟩
  let descriptor :=
    (exists_rawRouteDescriptor continuous taggedIncidenceMember).some
  have sourceSimple := refinedRouteFamily_routesSimple presentation
    (refinedRoute continuous.routes
      descriptor.metadata.sourceClauseIndex descriptor.sourceLiteralIndex)
    (List.fst_mem_of_mem_zipIdx descriptor.sourceTaggedRouteMember)
  have fragmentSimple := descriptor.fragment.routeIsSimple
    (refinedRoute continuous.routes
      descriptor.metadata.sourceClauseIndex descriptor.sourceLiteralIndex)
    descriptor.sourceRoute_length_ge_four sourceSimple
  have translatedSimple := routeIsSimple_translate fragmentSimple
    ((refinedIncidenceDrawing continuous).periodTranslation
      descriptor.latticeShift)
  have taggedSimple : LocalIncidenceDrawing.RouteIsSimple taggedRoute.1 := by
    rw [routeEq, descriptor.routeEq]
    exact translatedSimple
  simpa [taggedRoute] using taggedSimple

/-- The complete raw split drawing has endpoint-only listed-point contacts. -/
theorem rawIncidenceDrawing_routePointsMeetOnlyAtEndpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps) :
    (rawIncidenceDrawing
      presentation.toContinuousPlanarIncidencePresentation)
        |>.RoutePointsMeetOnlyAtEndpoints :=
  PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
    (rawIncidenceDrawing_liftedRoutesAvoidEachOther
      presentation sourceUnitSteps)
    (rawIncidenceDrawing_routesSimple presentation)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
