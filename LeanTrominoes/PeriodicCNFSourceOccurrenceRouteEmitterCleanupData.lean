/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterTapes

/-! # Data operations for final source-occurrence route-emitter cleanup -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def CleanupStage.symbols :
    (stage : CleanupStage) → TapeData → List (Alphabet stage.stack)
  | .input, data => data.input
  | .occurrenceReverse, data => data.occurrenceReverse
  | .occurrences, data => data.occurrences
  | .targetReverse, data => data.targetReverse
  | .targets, data => data.targets
  | .clauseCount, data => data.clauseCount
  | .literalCount, data => data.literalCount
  | .clauseIndex, data => data.clauseIndex
  | .edgeIndex, data => data.edgeIndex
  | .scratch, data => data.scratch
  | .outputReverse, data => data.outputReverse

def CleanupStage.set : (stage : CleanupStage) → TapeData →
    List (Alphabet stage.stack) → TapeData
  | .input, data, value => { data with input := value }
  | .occurrenceReverse, data, value =>
      { data with occurrenceReverse := value }
  | .occurrences, data, value => { data with occurrences := value }
  | .targetReverse, data, value => { data with targetReverse := value }
  | .targets, data, value => { data with targets := value }
  | .clauseCount, data, value => { data with clauseCount := value }
  | .literalCount, data, value => { data with literalCount := value }
  | .clauseIndex, data, value => { data with clauseIndex := value }
  | .edgeIndex, data, value => { data with edgeIndex := value }
  | .scratch, data, value => { data with scratch := value }
  | .outputReverse, data, value => { data with outputReverse := value }

def CleanupStage.cleared (stage : CleanupStage) (data : TapeData) :
    TapeData :=
  stage.set data []

@[simp] theorem CleanupStage.symbols_set (stage : CleanupStage)
    (data : TapeData) (value : List (Alphabet stage.stack)) :
    stage.symbols (stage.set data value) = value := by
  cases stage <;> rfl

def CleanupStage.afterCfg (stage : CleanupStage) (cursor : Cursor)
    (data : TapeData) : machine.Cfg :=
  match stage with
  | .input => cleanupCfg .occurrenceReverse cursor (stage.cleared data)
  | .occurrenceReverse =>
      cleanupCfg .occurrences cursor (stage.cleared data)
  | .occurrences => cleanupCfg .targetReverse cursor (stage.cleared data)
  | .targetReverse => cleanupCfg .targets cursor (stage.cleared data)
  | .targets => cleanupCfg .clauseCount cursor (stage.cleared data)
  | .clauseCount => cleanupCfg .literalCount cursor (stage.cleared data)
  | .literalCount => cleanupCfg .clauseIndex cursor (stage.cleared data)
  | .clauseIndex => cleanupCfg .edgeIndex cursor (stage.cleared data)
  | .edgeIndex => cleanupCfg .scratch cursor (stage.cleared data)
  | .scratch => cleanupCfg .outputReverse cursor (stage.cleared data)
  | .outputReverse => haltDataCfg initialCursor (stage.cleared data)

/-- The canonical final tape contents: only the forward output survives. -/
def cleanedData (data : TapeData) : TapeData :=
  ⟨[], [], [], [], [], [], [], [], [], [], [], data.output⟩

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
