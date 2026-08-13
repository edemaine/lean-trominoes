/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceCrossClauseSameTargetSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSpokeIdentification

/-!
# Angular order of final direct-source choices

The same-target atlas theorem assumes that occurrence slots increase in the
same direction as retained terminal-direction ranks.  Final coordinated
slots are computed from the angular occurrence order of the actual scaled
source routes.  This file proves that a successful final direct-source choice
therefore satisfies precisely the local atlas assumption.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicThreeSATThree

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- Every direct atlas incidence has a successful retained-terminal
classification, with the total local terminal datum as its exact result. -/
theorem retainedDirectSourceLocalRouteAt_terminalClassify :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (retainedDirectSourceLocalRouteAt kind index)) =
        some (retainedDirectSourceLocalTerminalAt kind index) := by
  native_decide

/-- The direction stored in an atlas choice is the direction component of
its classified local terminal datum. -/
theorem retainedDirectSourcePrefixChoiceAt_direction_eq_localTerminal
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    (retainedDirectSourcePrefixChoiceAt kind index).direction =
      (retainedDirectSourceLocalTerminalAt kind index).1 := by
  have equal :=
    congrArg Prod.fst
      (retainedDirectSourceFanTerminalAt_eq_scale kind index)
  simpa [retainedDirectSourceFanTerminalAt,
    scaleRetainedTerminalData] using equal

/-- A successful final choice classifies the terminal vector of its actual
scaled final incidence route with the choice's atlas direction. -/
theorem retainedFinalDirectSourceRouteChoice_scaledRoute_terminalClassify
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    (factor : Nat)
    (factorPositive : 0 < factor) :
    retainedTerminalDirectionClassify
        (routeTerminalVector
          (scalePolyline factor
            (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
              formula clauseIndex literalIndex))) =
      some
        ((retainedDirectSourcePrefixChoiceAt
            choice.kind choice.index).direction,
          factor *
            (retainedDirectSourceLocalTerminalAt
              choice.kind choice.index).2) := by
  have represents :=
    retainedFinalDirectSourceRouteChoice_representsFinalRoute
      formula clauseIndex literalIndex choice choiceLookup
  unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute
    at represents
  have unscaled :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
              formula clauseIndex literalIndex)) =
        some
          (retainedDirectSourceLocalTerminalAt
            choice.kind choice.index) := by
    rw [← represents, routeTerminalVector_translatePolyline]
    exact
      retainedDirectSourceLocalRouteAt_terminalClassify
        choice.kind choice.index
  have scaled :=
    retainedTerminalDirectionClassify_scale
      factorPositive unscaled
  rw [routeTerminalVector_scalePolyline]
  simpa [scaleRetainedTerminalData,
    retainedDirectSourcePrefixChoiceAt_direction_eq_localTerminal]
    using scaled

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Distinct genuine final occurrences of one atom give angular-order
compatible atlas choices and bounded coordinated slots. -/
theorem retainedFinalDirectSourceRouteChoices_angularOrderCompatible
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (atomsEqual : firstLiteral.atom = secondLiteral.atom)
    (occurrencesDifferent :
      (firstClauseIndex, firstLiteralIndex) ≠
        (secondClauseIndex, secondLiteralIndex)) :
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex
    firstChoice.AngularOrderCompatible
      secondChoice firstSlot secondSlot := by
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order := angularOccurrenceOrder source.erase routes
  let firstOccurrence :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
  let secondOccurrence :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (firstLiteral.atom, secondClauseIndex, secondLiteralIndex)
  let ordered :=
    order.copies firstLiteral.atom
  let firstIndex := ordered.idxOf firstOccurrence
  let secondIndex := ordered.idxOf secondOccurrence
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  have firstScaledClauseMember :
      (firstClause.scale retainedAngularFanSourceClearanceFactor,
          firstClauseIndex) ∈ source.clauses.zipIdx := by
    dsimp only [source]
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(firstClause, firstClauseIndex),
        firstClauseMember, rfl⟩
  have secondScaledClauseMember :
      (secondClause.scale retainedAngularFanSourceClearanceFactor,
          secondClauseIndex) ∈ source.clauses.zipIdx := by
    dsimp only [source]
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(secondClause, secondClauseIndex),
        secondClauseMember, rfl⟩
  have firstTagged :=
    taggedLiteral_mem_of_positioned_members
      source firstScaledClauseMember firstLiteralMember
  have secondTagged :=
    taggedLiteral_mem_of_positioned_members
      source secondScaledClauseMember secondLiteralMember
  have firstOccurrenceMember :
      firstOccurrence ∈
        occurrenceVariables source.erase firstLiteral.atom := by
    exact occurrenceVariables_mem _ firstTagged
  have secondOccurrenceMember :
      secondOccurrence ∈
        occurrenceVariables source.erase firstLiteral.atom := by
    simpa [secondOccurrence, atomsEqual] using
      (occurrenceVariables_mem _ secondTagged)
  have firstOrderedMember : firstOccurrence ∈ ordered := by
    exact
      (order.mem_iff firstLiteral.atom firstOccurrence).mpr
        firstOccurrenceMember
  have secondOrderedMember : secondOccurrence ∈ ordered := by
    exact
      (order.mem_iff firstLiteral.atom secondOccurrence).mpr
        secondOccurrenceMember
  have firstIndexLt : firstIndex < ordered.length := by
    exact List.idxOf_lt_length_of_mem firstOrderedMember
  have secondIndexLt : secondIndex < ordered.length := by
    exact List.idxOf_lt_length_of_mem secondOrderedMember
  have occurrenceValuesDifferent :
      firstOccurrence ≠ secondOccurrence := by
    intro equal
    apply occurrencesDifferent
    exact Prod.ext
      (congrArg (fun occurrence => occurrence.2.1) equal)
      (congrArg (fun occurrence => occurrence.2.2) equal)
  have indicesDifferent : firstIndex ≠ secondIndex := by
    intro equal
    apply occurrenceValuesDifferent
    exact idxOf_injective_on ordered
      firstOrderedMember secondOrderedMember equal
  have firstSlotVal : firstSlot.val = firstIndex := by
    simpa [source, routes, order, ordered, firstIndex,
      firstSlot, angularOccurrenceIndex, indexedOccurrence,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondSlotVal : secondSlot.val = secondIndex := by
    simpa [source, routes, order, ordered, secondIndex,
      secondSlot, angularOccurrenceIndex, indexedOccurrence,
      secondOccurrence, atomsEqual,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstClassified :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes firstOccurrence) =
        some
          ((retainedDirectSourcePrefixChoiceAt
              firstChoice.kind firstChoice.index).direction,
            retainedAngularFanSourceClearanceFactor *
              (retainedDirectSourceLocalTerminalAt
                firstChoice.kind firstChoice.index).2) := by
    simpa [routes, firstOccurrence, occurrenceTerminalVector,
      PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
      finalCoordinatedSourceRoutes] using
      retainedFinalDirectSourceRouteChoice_scaledRoute_terminalClassify
        formula firstClauseIndex firstLiteralIndex
        firstChoice firstChoiceLookup
        retainedAngularFanSourceClearanceFactor
        retainedAngularFanSourceClearanceFactor_pos
  have secondClassified :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes secondOccurrence) =
        some
          ((retainedDirectSourcePrefixChoiceAt
              secondChoice.kind secondChoice.index).direction,
            retainedAngularFanSourceClearanceFactor *
              (retainedDirectSourceLocalTerminalAt
                secondChoice.kind secondChoice.index).2) := by
    simpa [routes, secondOccurrence, occurrenceTerminalVector,
      PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
      finalCoordinatedSourceRoutes] using
      retainedFinalDirectSourceRouteChoice_scaledRoute_terminalClassify
        formula secondClauseIndex secondLiteralIndex
        secondChoice secondChoiceLookup
        retainedAngularFanSourceClearanceFactor
        retainedAngularFanSourceClearanceFactor_pos
  rcases lt_or_gt_of_ne indicesDifferent with before | after
  · have orderedAngle :
        occurrenceAngleLE routes
            (angularOccurrenceVariables
              source.erase routes firstLiteral.atom)[firstIndex]
            (angularOccurrenceVariables
              source.erase routes firstLiteral.atom)[secondIndex] =
          true :=
      angularOccurrenceVariables_getElem_angleLE
        source.erase routes firstLiteral.atom
        firstIndex secondIndex
        (by simpa [ordered, order] using firstIndexLt)
        (by simpa [ordered, order] using secondIndexLt)
        before
    have occurrenceAngle :
        occurrenceAngleLE routes firstOccurrence secondOccurrence =
          true := by
      simpa [ordered, order, firstIndex, secondIndex] using orderedAngle
    have directionsLe :=
      occurrenceAngleLE_rank_le_of_classified
        routes firstOccurrence secondOccurrence
        firstClassified secondClassified occurrenceAngle
    exact Or.inl
      ⟨by omega, directionsLe⟩
  · have orderedAngle :
        occurrenceAngleLE routes
            (angularOccurrenceVariables
              source.erase routes firstLiteral.atom)[secondIndex]
            (angularOccurrenceVariables
              source.erase routes firstLiteral.atom)[firstIndex] =
          true :=
      angularOccurrenceVariables_getElem_angleLE
        source.erase routes firstLiteral.atom
        secondIndex firstIndex
        (by simpa [ordered, order] using secondIndexLt)
        (by simpa [ordered, order] using firstIndexLt)
        after
    have occurrenceAngle :
        occurrenceAngleLE routes secondOccurrence firstOccurrence =
          true := by
      simpa [ordered, order, firstIndex, secondIndex] using orderedAngle
    have directionsLe :=
      occurrenceAngleLE_rank_le_of_classified
        routes secondOccurrence firstOccurrence
        secondClassified firstClassified occurrenceAngle
    exact Or.inr
      ⟨by omega, directionsLe⟩

end PeriodicOrthocrossing
end LeanTrominoes
