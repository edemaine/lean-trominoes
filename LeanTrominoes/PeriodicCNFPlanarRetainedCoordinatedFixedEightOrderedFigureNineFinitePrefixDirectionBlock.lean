/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineClauseProfileTemplate
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionTranslation

/-!
# Finite prefix blocks for retained inherited Figure 9 routes

The actual local route metadata supplies a finite template incidence index.
Together with the source clause's canonical finite profile, this selects the
exact normalized local-plus-extended direction block.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile
open Gadget

set_option maxHeartbeats 2000000

local instance finitePrefixDirectionVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem selectedRoute_eq_of_drawing_eq
    (first second :
      EmbeddedCNFIncidenceDrawing
        PlanarOneInThreeNoUnitsFigureNine.FigureNineNoUnitsVariable)
    (drawingEq : first = second)
    (index : Fin second.incidences.length) :
    let castIndex : Fin first.incidences.length :=
      Fin.cast
        (congrArg
          (fun drawing :
            EmbeddedCNFIncidenceDrawing
              PlanarOneInThreeNoUnitsFigureNine.FigureNineNoUnitsVariable =>
            drawing.incidences.length)
          drawingEq.symm)
        index
    first.routeAt (first.incidenceAt castIndex) =
      second.routeAt (second.incidenceAt index) := by
  subst second
  rfl

/-- Every inherited incidence's complete finite prefix is selected by one
query over the canonical retained clause profile. -/
theorem
    retainedOrderedFixedEightFigureNineOwnInheritedFinitePrefix_directionBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clauseIndex literalIndex : Nat}
    (data :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex literalIndex) :
    let clearanceSource :=
      retainedFigureNineClearancePositionedFormula source
    let clearancePlacement :=
      retainedFigureNineClearancePlacement source
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        clearanceSource clearancePlacement
    let localRoute :=
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        clearanceSource clearancePlacement clauseIndex literalIndex
    let fanData :=
      PositionedPeriodicCNF.clauseExitFanData
        data.sourceClause data.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source)
    let slot := data.sourceSlot clearanceWidth
    let origin :=
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement data.sourceClause data.generatedClause
    let profile :=
      PeriodicCNF.FormulaShapeOfFormula.clauseProfile
        (PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles
          data.sourceClause.literals)
    ∃ templateIndex :
        Fin
          (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
            profile).incidences.length,
      unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint localRoute
              (fanData.translatedExtendedRoute origin slot))) =
        PlanarOneInThreeNoUnitsFigureNine.normalizedLocalExtendedDirectionBlock
          ⟨profile, templateIndex, fanData, slot⟩ := by
  dsimp only
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement clauseIndex literalIndex
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
  let slot := data.sourceSlot clearanceWidth
  let origin :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
      outputPlacement data.sourceClause data.generatedClause
  let profile :=
    PeriodicCNF.FormulaShapeOfFormula.clauseProfile
      (PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles
        data.sourceClause.literals)
  have sourceClauseNonempty : data.sourceClause.literals ≠ [] := by
    exact List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx data.sourceLiteralMember)
  have sourceClauseWidth : data.sourceClause.literals.length ≤ 3 :=
    data.sourceClause_width clearanceWidth
  have drawingEq :
      PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          profile =
        PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.sourceClause := by
    simpa only [profile] using
      PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile_clauseProfile_literalProfiles
        data.sourceClause sourceClauseNonempty sourceClauseWidth
  rcases
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_eq_translated_templateRoute_of_members
        clearanceSource clearancePlacement clearanceWidth
        data.generatedClauseMember data.generatedLiteralMember with
    ⟨metadata, concreteIndex, metadataLookup, metadataClause, localEq⟩
  have metadataEqual : metadata = data.metadata := by
    apply Option.some.inj
    exact metadataLookup.symm.trans data.metadataLookup
  subst metadata
  have sourceDrawingEq :
      PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.metadata.sourceClause =
        PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.sourceClause :=
    congrArg PlanarOneInThreeNoUnitsFigureNine.templateDrawing
      data.metadataSourceClause
  let sourceConcreteIndex :
      Fin
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.sourceClause).incidences.length :=
    Fin.cast
      (congrArg
        (fun drawing :
          EmbeddedCNFIncidenceDrawing
            PlanarOneInThreeNoUnitsFigureNine.FigureNineNoUnitsVariable =>
          drawing.incidences.length)
        sourceDrawingEq)
      concreteIndex
  have sourceSelectedRouteEq :
      (PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.sourceClause).routeAt
          ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
            data.sourceClause).incidenceAt sourceConcreteIndex) =
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.metadata.sourceClause).routeAt
          ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
            data.metadata.sourceClause).incidenceAt concreteIndex) := by
    simpa only [sourceConcreteIndex] using
      selectedRoute_eq_of_drawing_eq
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.sourceClause)
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.metadata.sourceClause)
        sourceDrawingEq.symm concreteIndex
  have originEq :
      Cell.sub
          (Cell.scale
            PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
            data.metadata.sourceClause.position)
          (outputPlacement.translation
            (PeriodicCNF.clauseAnchor data.metadata.clause.literals)) =
        origin := by
    rw [data.metadataSourceClause, data.metadataClause]
    rfl
  have localRouteEqConcrete :
      localRoute =
        translatePolyline origin
          ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
              data.sourceClause).routeAt
            ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
              data.sourceClause).incidenceAt sourceConcreteIndex)) := by
    calc
      localRoute =
          translatePolyline
            (Cell.sub
              (Cell.scale
                PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
                data.metadata.sourceClause.position)
              (outputPlacement.translation
                (PeriodicCNF.clauseAnchor data.metadata.clause.literals)))
            ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
                data.metadata.sourceClause).routeAt
              ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
                data.metadata.sourceClause).incidenceAt concreteIndex)) := by
        simpa only [localRoute, outputPlacement] using localEq
      _ = translatePolyline origin
          ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
              data.metadata.sourceClause).routeAt
            ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
              data.metadata.sourceClause).incidenceAt concreteIndex)) := by
        rw [originEq]
      _ = translatePolyline origin
          ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
              data.sourceClause).routeAt
            ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
              data.sourceClause).incidenceAt sourceConcreteIndex)) := by
        rw [sourceSelectedRouteEq]
  let templateIndex :
      Fin
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          profile).incidences.length :=
    Fin.cast
      (congrArg
        (fun drawing :
          EmbeddedCNFIncidenceDrawing
            PlanarOneInThreeNoUnitsFigureNine.FigureNineNoUnitsVariable =>
          drawing.incidences.length)
        drawingEq.symm)
      sourceConcreteIndex
  have selectedRouteEq :
      (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          profile).routeAt
          ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
            profile).incidenceAt templateIndex) =
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.sourceClause).routeAt
          ((PlanarOneInThreeNoUnitsFigureNine.templateDrawing
            data.sourceClause).incidenceAt sourceConcreteIndex) := by
    simpa only [templateIndex] using
      selectedRoute_eq_of_drawing_eq
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          profile)
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawing
          data.sourceClause)
        drawingEq sourceConcreteIndex
  have localRouteEqProfile :
      localRoute =
        translatePolyline origin
          ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
              profile).routeAt
            ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
              profile).incidenceAt templateIndex)) := by
    rw [localRouteEqConcrete, selectedRouteEq]
  have fanValid : fanData.IsValid :=
    retainedFigureNineClearance_clauseExitFanData_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data.sourceClauseMember sourceClauseNonempty
  have fanCount : fanData.count = data.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      data.sourceClause data.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
      (List.length_pos_iff.mpr sourceClauseNonempty)
      sourceClauseWidth
  have slotActive : fanData.SlotActive slot := by
    unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    exact data.sourceLiteralIndex_lt
  have localEndpoints :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
      clearanceSource clearancePlacement clearanceWidth
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      data.generatedClauseMember data.generatedLiteralMember
  have localNonempty : localRoute ≠ [] := by
    intro empty
    simp [localRoute, empty] at localEndpoints
  have localLast :
      localRoute.getLast? =
        some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition
              slot.val)) := by
    calc
      localRoute.getLast? =
          some
            (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
              clearanceSource clearancePlacement clauseIndex literalIndex) :=
        localEndpoints.2
      _ = some
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
            outputPlacement data.sourceClause data.generatedClause
            data.sourceLiteralIndex) := congrArg some data.localEndpoint
      _ = some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition
              slot.val)) := by
        simp only [
          PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort,
          origin, outputPlacement, slot,
          PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData.sourceSlot_val]
  have extendedHead :
      (fanData.translatedExtendedRoute origin slot).head? =
        some
          (Cell.add origin
            (PlanarOneInThreeNoUnitsFigureNine.sourceLocalPosition
              slot.val)) :=
    fanData.translatedExtendedRoute_head?
      origin fanValid slot slotActive
  have localOrthogonal : OrthogonalPolyline localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
      clearanceSource clearancePlacement clearanceWidth
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      data.generatedClauseMember data.generatedLiteralMember
  have extendedOrthogonal :
      OrthogonalPolyline
        (fanData.translatedExtendedRoute origin slot) :=
    fanData.translatedExtendedRoute_orthogonal
      origin fanValid slot slotActive
  have actualPrefixOrthogonal :
      OrthogonalPolyline
        (joinAtEndpoint localRoute
          (fanData.translatedExtendedRoute origin slot)) :=
    localOrthogonal.joinAtEndpoint extendedOrthogonal
      localLast extendedHead
  have actualPrefixNonempty :
      joinAtEndpoint localRoute
          (fanData.translatedExtendedRoute origin slot) ≠ [] := by
    intro empty
    have joinedEmpty :
        localRoute ++
            (fanData.translatedExtendedRoute origin slot).tail = [] := by
      simpa [joinAtEndpoint] using empty
    exact localNonempty (List.append_eq_nil_iff.mp joinedEmpty).1
  refine ⟨templateIndex, ?_⟩
  exact
    PlanarOneInThreeNoUnitsFigureNine.normalizedTranslatedLocalExtendedRoute_directionWord
      profile templateIndex fanData slot origin localRoute
      localRouteEqProfile actualPrefixNonempty actualPrefixOrthogonal

end PeriodicOrthocrossing
end LeanTrominoes
