import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedSourceOrbitMembership

/-!
# Recovering retained orbit conditions from translated sources

The source-orbit API constructs a retained target from a family-specific
orbit condition.  This file records the converse for an exact translated
source: if that source is already retained, its enumeration membership
recovers the required neighboring coordinates (or exact carrier-link
membership).

For routed-variable sources, the target arm enumeration may expose a
different route-occurrence witness.  Equality of the translated link's first
terminal identifies its translation coordinate, which is all the orbit
condition needs.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Exact retained membership of a translated source implies the
family-specific orbit condition used by automatic source reindexing. -/
theorem
    DrawingPlanarSATClauseSource.retainedOrbitCondition_of_periodTranslate_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (sourceMember : source.RetainedComponentMember formula)
    (shift : Cell)
    (translatedMember :
      (source.periodTranslate formula shift).RetainedComponentMember
        formula) :
    source.RetainedOrbitCondition formula shift := by
  let graph := PeriodicCNF.incidenceGraph formula
  cases source with
  | crossover crossing localClauseIndex =>
      change
        crossing.periodTranslate graph shift ∈
          orientedCrossingHalo graph at translatedMember
      rcases orientedCrossingHalo_sound graph translatedMember with
        ⟨_firstMember, _secondMember,
          firstNeighbor, secondNeighbor, _⟩
      exact ⟨firstNeighbor, secondNeighbor⟩
  | carrier link localClauseIndex =>
      exact translatedMember
  | bend routeBend localClauseIndex =>
      change
        routeBend.periodTranslate shift ∈
          (drawingRouteBends graph).dedup at translatedMember
      rw [List.mem_dedup] at translatedMember
      rcases List.mem_flatMap.mp translatedMember with
        ⟨taggedRoute, _taggedRouteMember, translatedMember⟩
      rcases List.mem_flatMap.mp translatedMember with
        ⟨targetTranslate, targetTranslateMember,
          translatedMember⟩
      have targetTranslateEq :
          (routeBend.periodTranslate shift).translate =
            targetTranslate :=
        (routeBendsAux_member_data
          taggedRoute.2 targetTranslate taggedRoute.1 0
          translatedMember).2.1
      have targetNeighbor :
          IsNeighborTranslation targetTranslate :=
        (mem_neighborTranslations_iff targetTranslate).mp
          targetTranslateMember
      change
        IsNeighborTranslation
          (Cell.add routeBend.translate shift)
      have translatedEq :
          Cell.add routeBend.translate shift = targetTranslate := by
        simpa [RouteBend.periodTranslate] using targetTranslateEq
      simpa only [translatedEq] using targetNeighbor
  | routedClause site =>
      change
        clauseRouteSitePeriodTranslate site shift ∈
          drawingClauseRouteSites formula at translatedMember
      rcases List.mem_flatMap.mp translatedMember with
        ⟨taggedClause, _taggedClauseMember, translatedMember⟩
      rcases List.mem_map.mp translatedMember with
        ⟨targetTranslate, targetTranslateMember, targetSiteEq⟩
      have targetNeighbor :
          IsNeighborTranslation targetTranslate :=
        (mem_neighborTranslations_iff targetTranslate).mp
          targetTranslateMember
      have translateEq :
          Cell.add site.2 shift = targetTranslate :=
        congrArg Prod.snd targetSiteEq.symm
      change IsNeighborTranslation (Cell.add site.2 shift)
      simpa only [translateEq] using targetNeighbor
  | routedVariable site armIndex arm link localClauseIndex =>
      change
        variableRouteSitePeriodTranslate site shift ∈
            drawingVariableRouteSites formula ∧
          (planarSATNodeLinkPeriodTranslate graph link shift,
              armIndex) ∈
            (routedVariableLinksAt formula
              (variableRouteSitePeriodTranslate site shift)).zipIdx ∧
          arm =
            (planarSATNodeLinkPeriodTranslate graph link shift).first.duplicatorArm
            at translatedMember
      rcases
          exists_routeOccurrence_of_routedVariableLinkMember
            formula site sourceMember.2.1 with
        ⟨sourceOccurrence, sourceOccurrenceMember,
          sourceLinkFirstEq⟩
      rcases
          exists_routeOccurrence_of_routedVariableLinkMember
            formula
            (variableRouteSitePeriodTranslate site shift)
            translatedMember.2.1 with
        ⟨targetOccurrence, targetOccurrenceMember,
          targetLinkFirstEq⟩
      have targetOccurrenceData :=
        variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
          formula
          (variableRouteSitePeriodTranslate site shift)
          targetOccurrenceMember
      have translatedTerminalEq :
          (sourceOccurrence.targetTerminal formula).periodTranslate
              shift =
            targetOccurrence.targetTerminal formula := by
        have linkFirstEq :
            link.first.periodTranslate graph shift =
              .carrier (.terminal
                (targetOccurrence.targetTerminal formula)) := by
          simpa only [planarSATNodeLinkPeriodTranslate] using
            targetLinkFirstEq
        rw [sourceLinkFirstEq] at linkFirstEq
        have carrierEq :
            CarrierNode.terminal
                ((sourceOccurrence.targetTerminal formula).periodTranslate
                  shift) =
              CarrierNode.terminal
                (targetOccurrence.targetTerminal formula) :=
          PlanarSATNode.carrier.inj
            (by
              simpa only [PlanarSATNode.periodTranslate,
                CarrierNode.periodTranslate] using linkFirstEq)
        exact CarrierNode.terminal.inj carrierEq
      have targetTranslateEq :
          targetOccurrence.translate =
            Cell.add sourceOccurrence.translate shift := by
        have translateEq :=
          congrArg SegmentTerminal.translate translatedTerminalEq
        change
          Cell.add sourceOccurrence.translate shift =
            targetOccurrence.translate at translateEq
        exact translateEq.symm
      refine
        ⟨sourceOccurrence, sourceOccurrenceMember,
          sourceLinkFirstEq, ?_⟩
      simpa only [← targetTranslateEq] using
        targetOccurrence.translate_neighbor
          formula targetOccurrenceData.1

/-- A retained source with the same component as the exact source translate
also implies the orbit condition.  This version permits enumeration-only
fields, notably the routed-variable arm index and local clause index, to
change at the retained-window boundary. -/
theorem
    DrawingPlanarSATClauseSource.retainedOrbitCondition_of_retainedTarget
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (sourceMember : source.RetainedComponentMember formula)
    (shift : Cell)
    (targetSource : DrawingPlanarSATClauseSource Variable)
    (targetMember : targetSource.RetainedComponentMember formula)
    (targetComponentEq :
      targetSource.component =
        (source.periodTranslate formula shift).component) :
    source.RetainedOrbitCondition formula shift := by
  let graph := PeriodicCNF.incidenceGraph formula
  cases source with
  | crossover crossing localClauseIndex =>
      cases targetSource with
      | crossover targetCrossing targetLocalClauseIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
          have targetCrossingEq :=
            DrawingPlanarSATComponent.crossover.inj targetComponentEq
          subst targetCrossing
          exact
            DrawingPlanarSATClauseSource.retainedOrbitCondition_of_periodTranslate_mem
              formula (.crossover crossing localClauseIndex)
              sourceMember shift targetMember
      | carrier targetLink targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | bend targetBend targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | routedClause targetSite =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | routedVariable targetSite targetArmIndex targetArm targetLink
          targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
  | carrier link localClauseIndex =>
      cases targetSource with
      | crossover targetCrossing targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | carrier targetLink targetLocalClauseIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
          have targetLinkEq :=
            DrawingPlanarSATComponent.carrier.inj targetComponentEq
          subst targetLink
          exact
            DrawingPlanarSATClauseSource.retainedOrbitCondition_of_periodTranslate_mem
              formula (.carrier link localClauseIndex)
              sourceMember shift targetMember
      | bend targetBend targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | routedClause targetSite =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | routedVariable targetSite targetArmIndex targetArm targetLink
          targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
  | bend routeBend localClauseIndex =>
      cases targetSource with
      | crossover targetCrossing targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | carrier targetLink targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | bend targetBend targetLocalClauseIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
          have targetBendEq :=
            DrawingPlanarSATComponent.bend.inj targetComponentEq
          subst targetBend
          exact
            DrawingPlanarSATClauseSource.retainedOrbitCondition_of_periodTranslate_mem
              formula (.bend routeBend localClauseIndex)
              sourceMember shift targetMember
      | routedClause targetSite =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | routedVariable targetSite targetArmIndex targetArm targetLink
          targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
  | routedClause site =>
      cases targetSource with
      | crossover targetCrossing targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | carrier targetLink targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | bend targetBend targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | routedClause targetSite =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
          have targetSiteEq :=
            DrawingPlanarSATComponent.routedClause.inj targetComponentEq
          subst targetSite
          exact
            DrawingPlanarSATClauseSource.retainedOrbitCondition_of_periodTranslate_mem
              formula (.routedClause site)
              sourceMember shift targetMember
      | routedVariable targetSite targetArmIndex targetArm targetLink
          targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
  | routedVariable site armIndex arm link localClauseIndex =>
      cases targetSource with
      | crossover targetCrossing targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | carrier targetLink targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | bend targetBend targetLocalClauseIndex =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | routedClause targetSite =>
          simp [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate] at targetComponentEq
      | routedVariable targetSite targetArmIndex targetArm targetLink
          targetLocalClauseIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATClauseSource.periodTranslate,
            DrawingPlanarSATComponent.routedVariable.injEq] at targetComponentEq
          rcases targetComponentEq with
            ⟨targetSiteEq, targetArmEq, targetLinkEq⟩
          subst targetSite
          subst targetArm
          subst targetLink
          change
            variableRouteSitePeriodTranslate site shift ∈
                drawingVariableRouteSites formula ∧
              (planarSATNodeLinkPeriodTranslate graph link shift,
                  targetArmIndex) ∈
                (routedVariableLinksAt formula
                  (variableRouteSitePeriodTranslate site shift)).zipIdx ∧
              arm =
                (planarSATNodeLinkPeriodTranslate
                  graph link shift).first.duplicatorArm at targetMember
          rcases
              exists_routeOccurrence_of_routedVariableLinkMember
                formula site sourceMember.2.1 with
            ⟨sourceOccurrence, sourceOccurrenceMember,
              sourceLinkFirstEq⟩
          rcases
              exists_routeOccurrence_of_routedVariableLinkMember
                formula
                (variableRouteSitePeriodTranslate site shift)
                targetMember.2.1 with
            ⟨targetOccurrence, targetOccurrenceMember,
              targetLinkFirstEq⟩
          have targetOccurrenceData :=
            variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
              formula
              (variableRouteSitePeriodTranslate site shift)
              targetOccurrenceMember
          have translatedTerminalEq :
              (sourceOccurrence.targetTerminal formula).periodTranslate
                  shift =
                targetOccurrence.targetTerminal formula := by
            have linkFirstEq :
                link.first.periodTranslate graph shift =
                  .carrier (.terminal
                    (targetOccurrence.targetTerminal formula)) := by
              simpa only [planarSATNodeLinkPeriodTranslate] using
                targetLinkFirstEq
            rw [sourceLinkFirstEq] at linkFirstEq
            have carrierEq :
                CarrierNode.terminal
                    ((sourceOccurrence.targetTerminal
                      formula).periodTranslate shift) =
                  CarrierNode.terminal
                    (targetOccurrence.targetTerminal formula) :=
              PlanarSATNode.carrier.inj
                (by
                  simpa only [PlanarSATNode.periodTranslate,
                    CarrierNode.periodTranslate] using linkFirstEq)
            exact CarrierNode.terminal.inj carrierEq
          have targetTranslateEq :
              targetOccurrence.translate =
                Cell.add sourceOccurrence.translate shift := by
            have translateEq :=
              congrArg SegmentTerminal.translate translatedTerminalEq
            change
              Cell.add sourceOccurrence.translate shift =
                targetOccurrence.translate at translateEq
            exact translateEq.symm
          refine
            ⟨sourceOccurrence, sourceOccurrenceMember,
              sourceLinkFirstEq, ?_⟩
          simpa only [← targetTranslateEq] using
            targetOccurrence.translate_neighbor
              formula targetOccurrenceData.1

end PeriodicOrthocrossing
end LeanTrominoes
