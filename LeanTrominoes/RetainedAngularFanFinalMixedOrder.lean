/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSharedTargetData

/-!
# Angular order of final direct/fallback pairs

A successful direct atlas choice and a fallback route still participate in
the same final occurrence ordering.  This file transports that ordering to
the direct choice's stored terminal direction and the fallback route's
classified terminal direction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The occurrence slots and the direct/fallback terminal-direction ranks
increase in the same one of the two possible orientations. -/
def RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
    (choice : RetainedDirectSourceRouteChoice)
    (fallbackDirection : RetainedTerminalDirection)
    (directSlot fallbackSlot : RetainedTerminalSlot) : Prop :=
  let directDirection :=
    (retainedDirectSourcePrefixChoiceAt
      choice.kind choice.index).direction
  (directSlot.val < fallbackSlot.val ∧
      directDirection.angularRank ≤ fallbackDirection.angularRank) ∨
    (fallbackSlot.val < directSlot.val ∧
      fallbackDirection.angularRank ≤ directDirection.angularRank)

instance
    (choice : RetainedDirectSourceRouteChoice)
    (fallbackDirection : RetainedTerminalDirection)
    (directSlot fallbackSlot : RetainedTerminalSlot) :
    Decidable
      (RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
        choice fallbackDirection directSlot fallbackSlot) := by
  unfold RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
  infer_instance

/-- Different genuine final occurrences of one atom give compatible
coordinated slots and direct/fallback terminal-direction ranks. -/
theorem retainedFinalDirectFallback_angularOrderCompatible
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex =
        some choice)
    (atomsEqual : directLiteral.atom = fallbackLiteral.atom)
    (occurrencesDifferent :
      (directClauseIndex, directLiteralIndex) ≠
        (fallbackClauseIndex, fallbackLiteralIndex)) :
    let fallbackDirection :=
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1
    let directSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex
    let fallbackSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
    RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
      choice fallbackDirection directSlot fallbackSlot := by
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order := angularOccurrenceOrder source.erase routes
  let directOccurrence :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (directLiteral.atom, directClauseIndex, directLiteralIndex)
  let fallbackOccurrence :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (directLiteral.atom, fallbackClauseIndex, fallbackLiteralIndex)
  let ordered := order.copies directLiteral.atom
  let directIndex := ordered.idxOf directOccurrence
  let fallbackIndex := ordered.idxOf fallbackOccurrence
  let directSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula directLiteral directClauseIndex directLiteralIndex
  let fallbackSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
  let fallbackTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector
        (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex))
  have directScaledClauseMember :
      (directClause.scale retainedAngularFanSourceClearanceFactor,
          directClauseIndex) ∈ source.clauses.zipIdx := by
    dsimp only [source]
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(directClause, directClauseIndex),
        directClauseMember, rfl⟩
  have fallbackScaledClauseMember :
      (fallbackClause.scale retainedAngularFanSourceClearanceFactor,
          fallbackClauseIndex) ∈ source.clauses.zipIdx := by
    dsimp only [source]
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(fallbackClause, fallbackClauseIndex),
        fallbackClauseMember, rfl⟩
  have directTagged :=
    taggedLiteral_mem_of_positioned_members
      source directScaledClauseMember directLiteralMember
  have fallbackTagged :=
    taggedLiteral_mem_of_positioned_members
      source fallbackScaledClauseMember fallbackLiteralMember
  have directOccurrenceMember :
      directOccurrence ∈
        occurrenceVariables source.erase directLiteral.atom := by
    exact occurrenceVariables_mem _ directTagged
  have fallbackOccurrenceMember :
      fallbackOccurrence ∈
        occurrenceVariables source.erase directLiteral.atom := by
    simpa [fallbackOccurrence, atomsEqual] using
      (occurrenceVariables_mem _ fallbackTagged)
  have directOrderedMember : directOccurrence ∈ ordered := by
    exact
      (order.mem_iff directLiteral.atom directOccurrence).mpr
        directOccurrenceMember
  have fallbackOrderedMember : fallbackOccurrence ∈ ordered := by
    exact
      (order.mem_iff directLiteral.atom fallbackOccurrence).mpr
        fallbackOccurrenceMember
  have directIndexLt : directIndex < ordered.length := by
    exact List.idxOf_lt_length_of_mem directOrderedMember
  have fallbackIndexLt : fallbackIndex < ordered.length := by
    exact List.idxOf_lt_length_of_mem fallbackOrderedMember
  have occurrenceValuesDifferent :
      directOccurrence ≠ fallbackOccurrence := by
    intro equal
    apply occurrencesDifferent
    exact Prod.ext
      (congrArg (fun occurrence => occurrence.2.1) equal)
      (congrArg (fun occurrence => occurrence.2.2) equal)
  have indicesDifferent : directIndex ≠ fallbackIndex := by
    intro equal
    apply occurrenceValuesDifferent
    exact idxOf_injective_on ordered
      directOrderedMember fallbackOrderedMember equal
  have directSlotVal : directSlot.val = directIndex := by
    simpa [source, routes, order, ordered, directIndex,
      directSlot, angularOccurrenceIndex, indexedOccurrence,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackSlotVal : fallbackSlot.val = fallbackIndex := by
    simpa [source, routes, order, ordered, fallbackIndex,
      fallbackSlot, angularOccurrenceIndex, indexedOccurrence,
      fallbackOccurrence, atomsEqual,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have directClassified :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes directOccurrence) =
        some
          ((retainedDirectSourcePrefixChoiceAt
              choice.kind choice.index).direction,
            retainedAngularFanSourceClearanceFactor *
              (retainedDirectSourceLocalTerminalAt
                choice.kind choice.index).2) := by
    simpa [routes, directOccurrence, occurrenceTerminalVector,
      PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
      finalCoordinatedSourceRoutes] using
      retainedFinalDirectSourceRouteChoice_scaledRoute_terminalClassify
        formula directClauseIndex directLiteralIndex
        choice choiceLookup retainedAngularFanSourceClearanceFactor
        retainedAngularFanSourceClearanceFactor_pos
  have fallbackClassified :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes fallbackOccurrence) =
        some
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor fallbackTerminal) := by
    simpa [routes, fallbackOccurrence, occurrenceTerminalVector,
      PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
      fallbackTerminal, finalCoordinatedSourceRoutes] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        fallbackClauseMember fallbackLiteralMember
  rcases lt_or_gt_of_ne indicesDifferent with before | after
  · have orderedAngle :
        occurrenceAngleLE routes
            (angularOccurrenceVariables
              source.erase routes directLiteral.atom)[directIndex]
            (angularOccurrenceVariables
              source.erase routes directLiteral.atom)[fallbackIndex] =
          true :=
      angularOccurrenceVariables_getElem_angleLE
        source.erase routes directLiteral.atom
        directIndex fallbackIndex
        (by simpa [ordered, order] using directIndexLt)
        (by simpa [ordered, order] using fallbackIndexLt)
        before
    have occurrenceAngle :
        occurrenceAngleLE routes directOccurrence fallbackOccurrence =
          true := by
      simpa [ordered, order, directIndex, fallbackIndex] using
        orderedAngle
    have directionsLe :=
      occurrenceAngleLE_rank_le_of_classified
        routes directOccurrence fallbackOccurrence
        directClassified fallbackClassified occurrenceAngle
    exact Or.inl
      ⟨by omega,
        by
          simpa [fallbackTerminal, scaleRetainedTerminalData] using
            directionsLe⟩
  · have orderedAngle :
        occurrenceAngleLE routes
            (angularOccurrenceVariables
              source.erase routes directLiteral.atom)[fallbackIndex]
            (angularOccurrenceVariables
              source.erase routes directLiteral.atom)[directIndex] =
          true :=
      angularOccurrenceVariables_getElem_angleLE
        source.erase routes directLiteral.atom
        fallbackIndex directIndex
        (by simpa [ordered, order] using fallbackIndexLt)
        (by simpa [ordered, order] using directIndexLt)
        after
    have occurrenceAngle :
        occurrenceAngleLE routes fallbackOccurrence directOccurrence =
          true := by
      simpa [ordered, order, directIndex, fallbackIndex] using
        orderedAngle
    have directionsLe :=
      occurrenceAngleLE_rank_le_of_classified
        routes fallbackOccurrence directOccurrence
        fallbackClassified directClassified occurrenceAngle
    exact Or.inr
      ⟨by omega,
        by
          simpa [fallbackTerminal, scaleRetainedTerminalData] using
            directionsLe⟩

/-- Equality of the canonical final variable centers supplies the atom
equality required by the mixed angular-order theorem. -/
theorem
    retainedFinalDirectFallback_angularOrderCompatible_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex =
        some choice)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral) :
    let fallbackDirection :=
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1
    let directSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex
    let fallbackSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
    RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
      choice fallbackDirection directSlot fallbackSlot := by
  have atomsEqual :
      directLiteral.atom = fallbackLiteral.atom :=
    retainedFinalCanonicalLiteralPositions_eq_imp_atoms_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember centersEqual
  apply
    retainedFinalDirectFallback_angularOrderCompatible
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      choiceLookup atomsEqual
  intro occurrencesEqual
  apply clauseIndicesDifferent
  exact congrArg Prod.fst occurrencesEqual

end PeriodicOrthocrossing
end LeanTrominoes
