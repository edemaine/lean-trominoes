/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterParseLeftExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterParseRightExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRestoreOccurrencesExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRestoreTargetsExecution

/-! # Parsing a separated occurrence/target stream -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def parseTime (occurrences : List OccurrenceToken)
    (targets : List UnarySymbol) : Nat :=
  4 * occurrences.length + 4 * targets.length + 4

def parsing_evalsInTime (occurrences : List OccurrenceToken)
    (targets : List UnarySymbol) :
    EvalsToInTime machine.step
      (scanLeftCfg initialCursor
        ⟨occurrences.map .left ++ .separator :: targets.map .right,
          [], [], [], [], [], [], [], [], [], [], []⟩)
      (some (scanOccurrencesCfg initialCursor
        ⟨[], [], occurrences, [], targets,
          countTape SourceOccurrenceRouteTokens.isClause occurrences,
          countTape SourceOccurrenceRouteTokens.isLiteral occurrences,
          [], [], [], [], []⟩))
      (parseTime occurrences targets) := by
  let startData : TapeData :=
    ⟨occurrences.map .left ++ .separator :: targets.map .right,
      [], [], [], [], [], [], [], [], [], [], []⟩
  let afterLeft : TapeData :=
    ⟨targets.map .right, occurrences.reverse, [], [], [],
      countTape SourceOccurrenceRouteTokens.isClause occurrences,
      countTape SourceOccurrenceRouteTokens.isLiteral occurrences,
      [], [], [], [], []⟩
  let afterRight : TapeData :=
    ⟨[], occurrences.reverse, [], targets.reverse, [],
      countTape SourceOccurrenceRouteTokens.isClause occurrences,
      countTape SourceOccurrenceRouteTokens.isLiteral occurrences,
      [], [], [], [], []⟩
  let afterOccurrences : TapeData :=
    ⟨[], [], occurrences, targets.reverse, [],
      countTape SourceOccurrenceRouteTokens.isClause occurrences,
      countTape SourceOccurrenceRouteTokens.isLiteral occurrences,
      [], [], [], [], []⟩
  let parsedData : TapeData :=
    ⟨[], [], occurrences, [], targets,
      countTape SourceOccurrenceRouteTokens.isClause occurrences,
      countTape SourceOccurrenceRouteTokens.isLiteral occurrences,
      [], [], [], [], []⟩
  have leftRun := scanLeft_evalsInTime initialCursor occurrences
    (targets.map .right) startData rfl
  have leftRun' : EvalsToInTime machine.step
      (scanLeftCfg initialCursor startData)
      (some (scanRightCfg initialCursor afterLeft))
      (2 * occurrences.length + 1) := by
    simpa [startData, afterLeft] using leftRun
  have rightRun := scanRight_evalsInTime initialCursor targets afterLeft rfl
  have rightRun' : EvalsToInTime machine.step
      (scanRightCfg initialCursor afterLeft)
      (some (restoreOccurrencesCfg initialCursor afterRight))
      (2 * targets.length + 1) := by
    simpa [afterLeft, afterRight] using rightRun
  have throughRight := EvalsToInTime.trans machine.step
    (2 * occurrences.length + 1) (2 * targets.length + 1)
    _ _ _ leftRun' rightRun'
  have occurrencesRun := restoreOccurrences_evalsInTime initialCursor
    occurrences.reverse afterRight rfl
  have occurrencesRun' : EvalsToInTime machine.step
      (restoreOccurrencesCfg initialCursor afterRight)
      (some (restoreTargetsCfg initialCursor afterOccurrences))
      (2 * occurrences.length + 1) := by
    simpa [afterRight, afterOccurrences] using occurrencesRun
  have throughOccurrences := EvalsToInTime.trans machine.step
    (2 * targets.length + 1 + (2 * occurrences.length + 1))
    (2 * occurrences.length + 1) _ _ _ throughRight occurrencesRun'
  have targetsRun := restoreTargets_evalsInTime initialCursor
    targets.reverse afterOccurrences rfl
  have targetsRun' : EvalsToInTime machine.step
      (restoreTargetsCfg initialCursor afterOccurrences)
      (some (scanOccurrencesCfg initialCursor parsedData))
      (2 * targets.length + 1) := by
    simpa [afterOccurrences, parsedData] using targetsRun
  have whole := EvalsToInTime.trans machine.step
    (2 * occurrences.length + 1 +
      (2 * targets.length + 1 + (2 * occurrences.length + 1)))
    (2 * targets.length + 1) _ _ _ throughOccurrences targetsRun'
  convert whole using 1
  simp [parseTime]
  omega

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
