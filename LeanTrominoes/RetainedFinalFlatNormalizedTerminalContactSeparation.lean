/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedDirectSourceEqualityLensFinalSegmentSeparation
import LeanTrominoes.RetainedAngularFanDirectSourceCarrierBoundarySeparation

/-!
# Terminal rectangles at normalized carrier contacts

A direct anchor-normalized macrocell route can be reselected from its local
incidence drawing, yielding an exact finite direct-atlas route in the same
physical frame.  At a genuine carrier contact, the contact certificate says
that this macrocell origin is one endpoint origin of the normalized equality
lens.  The finite equality-lens theorem can therefore be applied directly to
the two selected final segments.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

set_option maxHeartbeats 2000000

/-- An exact direct-atlas representation recovered from a normalized direct
macrocell source. -/
structure FinalGaugedFlatNormalizedDirectChoiceData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell) where
  selection :
    FinalGaugedFlatNormalizedRouteSelection
      formula taggedRoute normalized.source
  choice : RetainedDirectSourceRouteChoice
  lookup :
    retainedDirectSourceRouteChoice?
        formula normalized.source selection.literalIndex =
      some choice
  routeEq :
    translatePolyline choice.origin
        (retainedDirectSourceLocalRouteAt choice.kind choice.index) =
      taggedRoute.1

/-- Every normalized direct source has an exact local-atlas representation
of its selected final route. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.exists_directChoiceData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell)
    (direct : normalized.source.component.IsDirect) :
    Nonempty
      (FinalGaugedFlatNormalizedDirectChoiceData
        formula normalized) := by
  rcases normalized.exists_routeSelection
      formula wellFormed degree isLocal with
    ⟨selection⟩
  let metadata : DrawingPlanarSATClauseMetadata Variable :=
    ⟨selection.clause, normalized.source⟩
  have clauseFormulaMember :
      (selection.clause, normalized.source.localClauseIndex) ∈
        (normalized.source.clauseFormula formula).zipIdx := by
    rw [←
      retainedComponentMember_incidenceDrawing_formula_eq_clauseFormula
        formula wellFormed degree isLocal
        normalized.source normalized.sourceMember]
    exact selection.clauseMember
  have valid : metadata.RetainedValid formula := by
    apply
      (metadata.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mpr
    exact ⟨normalized.sourceMember, clauseFormulaMember⟩
  rcases
      DrawingPlanarSATClauseMetadata.exists_retainedDirectSourceRouteChoice
        metadata valid selection.literalMember
        (normalized.directCases direct) with
    ⟨choice, lookup, _matches⟩
  have represents :=
    retainedDirectSourceRouteChoice?_represents_of_eq_some
      formula normalized.source selection.literalIndex choice lookup
  unfold RetainedDirectSourceRouteChoice.Represents at represents
  exact ⟨{
    selection := selection
    choice := choice
    lookup := lookup
    routeEq := represents.trans selection.routeEq.symm
  }⟩

/-- The final segment of the selected normalized route is exactly the
positioned source segment of its recovered atlas choice. -/
theorem FinalGaugedFlatNormalizedDirectChoiceData.finalSegment_eq_choice
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula taggedRoute}
    {normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell}
    (data :
      FinalGaugedFlatNormalizedDirectChoiceData formula normalized) :
    (⟨polylineLastEntrance taggedRoute.1,
        taggedRoute.1.getLastD (0, 0)⟩ : GridSegment) =
      data.choice.sourceSegment := by
  have localLength :=
    retainedDirectSourceLocalRouteAt_length
      data.choice.kind data.choice.index
  rcases List.length_eq_two.mp localLength with
    ⟨localHead, localLast, localRouteEq⟩
  rw [← data.routeEq]
  simp [localRouteEq, translatePolyline,
    polylineLastEntrance, polylineFirstExit,
    RetainedDirectSourceRouteChoice.sourceSegment]

/-- Obliqueness of the selected normalized final segment reflects to the
untranslated finite atlas segment. -/
theorem FinalGaugedFlatNormalizedDirectChoiceData.localSegment_not_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula taggedRoute}
    {normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell}
    (data :
      FinalGaugedFlatNormalizedDirectChoiceData formula normalized)
    (finalOblique :
      ¬(⟨polylineLastEntrance taggedRoute.1,
          taggedRoute.1.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    ¬(⟨(retainedDirectSourceLocalRouteAt
            data.choice.kind data.choice.index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt
            data.choice.kind data.choice.index).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned := by
  intro localAligned
  apply finalOblique
  rw [data.finalSegment_eq_choice]
  exact
    (GridSegment.isAxisAligned_translate
      (⟨(retainedDirectSourceLocalRouteAt
          data.choice.kind data.choice.index).headD (0, 0),
        (retainedDirectSourceLocalRouteAt
          data.choice.kind data.choice.index).getLastD (0, 0)⟩ :
        GridSegment)
      data.choice.origin).mpr localAligned

/-- A successful direct choice for a crossover source is positioned at that
crossover's macrocell origin. -/
theorem FinalGaugedFlatNormalizedDirectChoiceData.choice_origin_eq_crossover
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula taggedRoute}
    {normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell}
    (data :
      FinalGaugedFlatNormalizedDirectChoiceData formula normalized)
    {crossing : CrossingRecord}
    {localClauseIndex : Nat}
    (sourceEq : normalized.source = .crossover crossing localClauseIndex) :
    data.choice.origin = crossingMacroOrigin crossing := by
  let literalIndex : Nat := data.selection.literalIndex
  have lookup :
      retainedDirectSourceRouteChoice?
          formula normalized.source literalIndex = some data.choice :=
    data.lookup
  rw [sourceEq] at lookup
  simp [retainedDirectSourceRouteChoice?] at lookup
  rcases lookup with ⟨_, _, choiceEq⟩
  rw [← choiceEq]

/-- A successful direct choice for a routed-clause source is positioned at
that routed clause's macrocell origin. -/
theorem FinalGaugedFlatNormalizedDirectChoiceData.choice_origin_eq_routedClause
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula taggedRoute}
    {normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell}
    (data :
      FinalGaugedFlatNormalizedDirectChoiceData formula normalized)
    {site : ClauseRouteSite}
    (sourceEq : normalized.source = .routedClause site) :
    data.choice.origin = routedClauseOrigin formula site := by
  let literalIndex : Nat := data.selection.literalIndex
  have lookup :
      retainedDirectSourceRouteChoice?
          formula normalized.source literalIndex = some data.choice :=
    data.lookup
  rw [sourceEq] at lookup
  simp [retainedDirectSourceRouteChoice?] at lookup
  rcases lookup with ⟨_, choiceEq⟩
  rw [← choiceEq]

/-- A successful direct choice for a routed-variable source is positioned at
that routed variable's macrocell origin. -/
theorem FinalGaugedFlatNormalizedDirectChoiceData.choice_origin_eq_routedVariable
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula taggedRoute}
    {normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell}
    (data :
      FinalGaugedFlatNormalizedDirectChoiceData formula normalized)
    {site : VariableRouteSite Variable}
    {armIndex : Nat}
    {arm : DuplicatorArm}
    {link : EqualityLink (PlanarSATNode Variable)}
    {localClauseIndex : Nat}
    (sourceEq : normalized.source =
      .routedVariable site armIndex arm link localClauseIndex) :
    data.choice.origin = routedVariableOrigin formula site := by
  let literalIndex : Nat := data.selection.literalIndex
  have lookup :
      retainedDirectSourceRouteChoice?
          formula normalized.source literalIndex = some data.choice :=
    data.lookup
  rw [sourceEq] at lookup
  simp [retainedDirectSourceRouteChoice?] at lookup
  rcases lookup with ⟨_, _, choiceEq⟩
  rw [← choiceEq]

/-- Every clause in a carrier equality block has two literals. -/
private theorem carrierFormula_clause_literals_length
    {Variable : Type*}
    (link : EqualityLink CarrierNode)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    (clauseMember :
      clause ∈ drawingPlanarSATCarrierFormulaAt
        (Variable := Variable) link) :
    clause.literals.length = 2 := by
  simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
    EmbeddedClause.rename, EmbeddedClause.map] at clauseMember
  rcases clauseMember with clauseEq | clauseEq
  · subst clause
    simp
  · subst clause
    simp

/-- The selected normalized carrier route, exposed as an exact route of its
intrinsic equality lens with bounded presentation indices. -/
structure FinalGaugedFlatNormalizedCarrierLensData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness formula taggedRoute) where
  clauseIndex : Nat
  selection :
    FinalGaugedFlatNormalizedRouteSelection formula taggedRoute
      (.carrier carrier.normalizedLink clauseIndex)
  clauseIndexLt : clauseIndex < 2
  literalIndexLt : selection.literalIndex < 2
  routeEq :
    taggedRoute.1 =
      (EqualityLink.lensDrawing
        (CarrierNode.position formula.incidenceGraph)
        carrier.normalizedLink).routes
          clauseIndex selection.literalIndex

/-- Every normalized carrier witness supplies its intrinsic lens selection. -/
theorem FinalGaugedFlatCarrierRouteWitness.exists_normalizedCarrierLensData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness formula taggedRoute) :
    Nonempty
      (FinalGaugedFlatNormalizedCarrierLensData formula carrier) := by
  rcases carrier.exists_normalizedRouteSelection
      formula wellFormed degree isLocal with
    ⟨clauseIndex, ⟨selection⟩⟩
  have linkMember :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  have clauseIndexLt : clauseIndex < 2 := by
    have indexLt := List.snd_lt_of_mem_zipIdx selection.clauseMember
    change
      clauseIndex <
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrier.normalizedLink).formula.length
      at indexLt
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal linkMember] at indexLt
    simpa [drawingPlanarSATCarrierFormulaAt,
      equalityInstance] using indexLt
  have literalIndexLt : selection.literalIndex < 2 := by
    have indexLt := List.snd_lt_of_mem_zipIdx selection.literalMember
    have clauseMember :=
      List.fst_mem_of_mem_zipIdx selection.clauseMember
    change
      selection.clause ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrier.normalizedLink).formula
      at clauseMember
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal linkMember] at clauseMember
    rw [carrierFormula_clause_literals_length
      carrier.normalizedLink clauseMember] at indexLt
    exact indexLt
  refine ⟨{
    clauseIndex := clauseIndex
    selection := selection
    clauseIndexLt := clauseIndexLt
    literalIndexLt := literalIndexLt
    routeEq := ?_
  }⟩
  simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex,
    drawingPlanarSATCarrierLensIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename] using selection.routeEq

/-- Transport the finite first-end lens dichotomy to the two selected
normalized final segments once their physical origins are identified. -/
private theorem normalizedFinalSegments_firstEndpoint_dichotomy
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    {carrier :
      FinalGaugedFlatCarrierRouteWitness formula carrierTaggedRoute}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula macrocellTaggedRoute}
    {normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell}
    (carrierData :
      FinalGaugedFlatNormalizedCarrierLensData formula carrier)
    (directData :
      FinalGaugedFlatNormalizedDirectChoiceData formula normalized)
    (originEq :
      directData.choice.origin =
        EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position formula.incidenceGraph)
          carrier.normalizedLink)
    (macrocellFinalOblique :
      ¬(⟨polylineLastEntrance macrocellTaggedRoute.1,
          macrocellTaggedRoute.1.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierTaggedRoute.1,
        carrierTaggedRoute.1.getLastD (0, 0)⟩
    let macrocellFinal : GridSegment :=
      ⟨polylineLastEntrance macrocellTaggedRoute.1,
        macrocellTaggedRoute.1.getLastD (0, 0)⟩
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        macrocellFinal.coordinateLower macrocellFinal.coordinateUpper ∨
      carrierFinal.finish = macrocellFinal.finish := by
  have linkMember :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  have geometry :=
    retainedDrawingCompleteCarrierLinkRaw_lensGeometry
      wellFormed degree isLocal linkMember
  have localOblique :=
    directData.localSegment_not_axisAligned macrocellFinalOblique
  have dichotomy :=
    PeriodicEightOccurrenceSplit.EqualityLink.lensDrawing_first_finalSegmentRectanglesSeparated_or_finish_eq_nat
      geometry carrierData.clauseIndex carrierData.selection.literalIndex
      carrierData.clauseIndexLt carrierData.literalIndexLt
      directData.choice.kind directData.choice.index localOblique
  have positionedDirectEq :
      (⟨(retainedDirectSourceLocalRouteAt
            directData.choice.kind directData.choice.index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt
            directData.choice.kind directData.choice.index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (EqualityLink.firstCarrierMacroOrigin
            (CarrierNode.position formula.incidenceGraph)
            carrier.normalizedLink) =
        directData.choice.sourceSegment := by
    rw [← originEq]
    rfl
  rw [← carrierData.routeEq, positionedDirectEq,
    ← directData.finalSegment_eq_choice] at dichotomy
  exact dichotomy

/-- Transport the finite second-end lens dichotomy to the two selected
normalized final segments once their physical origins are identified. -/
private theorem normalizedFinalSegments_secondEndpoint_dichotomy
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    {carrier :
      FinalGaugedFlatCarrierRouteWitness formula carrierTaggedRoute}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula macrocellTaggedRoute}
    {normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell}
    (carrierData :
      FinalGaugedFlatNormalizedCarrierLensData formula carrier)
    (directData :
      FinalGaugedFlatNormalizedDirectChoiceData formula normalized)
    (originEq :
      directData.choice.origin =
        EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position formula.incidenceGraph)
          carrier.normalizedLink)
    (macrocellFinalOblique :
      ¬(⟨polylineLastEntrance macrocellTaggedRoute.1,
          macrocellTaggedRoute.1.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierTaggedRoute.1,
        carrierTaggedRoute.1.getLastD (0, 0)⟩
    let macrocellFinal : GridSegment :=
      ⟨polylineLastEntrance macrocellTaggedRoute.1,
        macrocellTaggedRoute.1.getLastD (0, 0)⟩
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        macrocellFinal.coordinateLower macrocellFinal.coordinateUpper ∨
      carrierFinal.finish = macrocellFinal.finish := by
  have linkMember :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  have geometry :=
    retainedDrawingCompleteCarrierLinkRaw_lensGeometry
      wellFormed degree isLocal linkMember
  have localOblique :=
    directData.localSegment_not_axisAligned macrocellFinalOblique
  have dichotomy :=
    PeriodicEightOccurrenceSplit.EqualityLink.lensDrawing_second_finalSegmentRectanglesSeparated_or_finish_eq_nat
      geometry carrierData.clauseIndex carrierData.selection.literalIndex
      carrierData.clauseIndexLt carrierData.literalIndexLt
      directData.choice.kind directData.choice.index localOblique
  have positionedDirectEq :
      (⟨(retainedDirectSourceLocalRouteAt
            directData.choice.kind directData.choice.index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt
            directData.choice.kind directData.choice.index).getLastD (0, 0)⟩ :
        GridSegment).translate
          (EqualityLink.secondCarrierMacroOrigin
            (CarrierNode.position formula.incidenceGraph)
            carrier.normalizedLink) =
        directData.choice.sourceSegment := by
    rw [← originEq]
    rfl
  rw [← carrierData.routeEq, positionedDirectEq,
    ← directData.finalSegment_eq_choice] at dichotomy
  exact dichotomy

/-- At every genuine normalized contact between a carrier route and an
oblique direct macrocell route, their final rectangles are strictly
separated unless the two routes have the same final endpoint. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.finalSegmentRectanglesSeparated_or_finish_eq_of_normalizedDirectContact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness formula macrocellTaggedRoute)
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource formula macrocell)
    (direct : normalized.source.component.IsDirect)
    (contact :
      FinalGaugedFlatNormalizedCarrierContact
        formula carrier macrocell normalized)
    (macrocellFinalOblique :
      ¬(⟨polylineLastEntrance macrocellTaggedRoute.1,
          macrocellTaggedRoute.1.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned) :
    let carrierFinal : GridSegment :=
      ⟨polylineLastEntrance carrierTaggedRoute.1,
        carrierTaggedRoute.1.getLastD (0, 0)⟩
    let macrocellFinal : GridSegment :=
      ⟨polylineLastEntrance macrocellTaggedRoute.1,
        macrocellTaggedRoute.1.getLastD (0, 0)⟩
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        macrocellFinal.coordinateLower macrocellFinal.coordinateUpper ∨
      carrierFinal.finish = macrocellFinal.finish := by
  rcases carrier.exists_normalizedCarrierLensData
      formula wellFormed degree isLocal with
    ⟨carrierData⟩
  rcases normalized.exists_directChoiceData
      formula wellFormed degree isLocal direct with
    ⟨directData⟩
  have linkMember :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  rcases contact with crossoverContact | terminalContact
  · rcases crossoverContact with
      ⟨crossing, localClauseIndex, sourceEq,
        side, firstEqual | secondEqual⟩
    · have directOrigin :=
        directData.choice_origin_eq_crossover sourceEq
      have carrierOrigin :=
        retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_boundary
          wellFormed degree isLocal linkMember firstEqual
      exact normalizedFinalSegments_firstEndpoint_dichotomy
        formula wellFormed degree isLocal carrierData directData
        (directOrigin.trans carrierOrigin.symm) macrocellFinalOblique
    · have directOrigin :=
        directData.choice_origin_eq_crossover sourceEq
      have carrierOrigin :=
        retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_boundary
          wellFormed degree isLocal linkMember secondEqual
      exact normalizedFinalSegments_secondEndpoint_dichotomy
        formula wellFormed degree isLocal carrierData directData
        (directOrigin.trans carrierOrigin.symm) macrocellFinalOblique
  · rcases terminalContact with routedClauseContact | routedVariableContact
    · rcases routedClauseContact with
        ⟨site, occurrence, sourceEq, occurrenceMember,
          firstEqual | secondEqual⟩
      · have directOrigin :=
          directData.choice_origin_eq_routedClause sourceEq
        have carrierOrigin :=
          (retainedDrawingCompleteCarrierLinkRaw_first_sourceTerminalInterface
            wellFormed degree isLocal linkMember site
            occurrenceMember firstEqual).2
        exact normalizedFinalSegments_firstEndpoint_dichotomy
          formula wellFormed degree isLocal carrierData directData
          (directOrigin.trans carrierOrigin.symm) macrocellFinalOblique
      · have directOrigin :=
          directData.choice_origin_eq_routedClause sourceEq
        have carrierOrigin :=
          (retainedDrawingCompleteCarrierLinkRaw_second_sourceTerminalInterface
            wellFormed degree isLocal linkMember site
            occurrenceMember secondEqual).2
        exact normalizedFinalSegments_secondEndpoint_dichotomy
          formula wellFormed degree isLocal carrierData directData
          (directOrigin.trans carrierOrigin.symm) macrocellFinalOblique
    · rcases routedVariableContact with
        ⟨site, armIndex, arm, link, localClauseIndex,
          occurrence, sourceEq, occurrenceMember,
          firstEqual | secondEqual⟩
      · have directOrigin :=
          directData.choice_origin_eq_routedVariable sourceEq
        have carrierOrigin :=
          (retainedDrawingCompleteCarrierLinkRaw_first_targetTerminalInterface
            wellFormed degree isLocal linkMember site
            occurrenceMember firstEqual).2
        exact normalizedFinalSegments_firstEndpoint_dichotomy
          formula wellFormed degree isLocal carrierData directData
          (directOrigin.trans carrierOrigin.symm) macrocellFinalOblique
      · have directOrigin :=
          directData.choice_origin_eq_routedVariable sourceEq
        have carrierOrigin :=
          (retainedDrawingCompleteCarrierLinkRaw_second_targetTerminalInterface
            wellFormed degree isLocal linkMember site
            occurrenceMember secondEqual).2
        exact normalizedFinalSegments_secondEndpoint_dichotomy
          formula wellFormed degree isLocal carrierData directData
          (directOrigin.trans carrierOrigin.symm) macrocellFinalOblique

end PeriodicOrthocrossing
end LeanTrominoes
