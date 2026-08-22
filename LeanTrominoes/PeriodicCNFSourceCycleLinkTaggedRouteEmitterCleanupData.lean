/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTapes

/-! # Data operations for final tagged cycle-link emitter cleanup -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def CleanupStage.symbols :
    (stage : CleanupStage) → TapeData → List (Alphabet stage.stack)
  | .input, data => data.input
  | .tagReverse, data => data.tagReverse
  | .tags, data => data.tags
  | .targetReverse, data => data.targetReverse
  | .targets, data => data.targets
  | .clauseCount, data => data.clauseCount
  | .literalCount, data => data.literalCount
  | .linkIndex, data => data.linkIndex
  | .scratch, data => data.scratch
  | .outputReverse, data => data.outputReverse

def CleanupStage.set : (stage : CleanupStage) → TapeData →
    List (Alphabet stage.stack) → TapeData
  | .input, data, value => { data with input := value }
  | .tagReverse, data, value => { data with tagReverse := value }
  | .tags, data, value => { data with tags := value }
  | .targetReverse, data, value => { data with targetReverse := value }
  | .targets, data, value => { data with targets := value }
  | .clauseCount, data, value => { data with clauseCount := value }
  | .literalCount, data, value => { data with literalCount := value }
  | .linkIndex, data, value => { data with linkIndex := value }
  | .scratch, data, value => { data with scratch := value }
  | .outputReverse, data, value => { data with outputReverse := value }

def CleanupStage.cleared (stage : CleanupStage) (data : TapeData) :
    TapeData :=
  stage.set data []

@[simp] theorem CleanupStage.symbols_set (stage : CleanupStage)
    (data : TapeData) (value : List (Alphabet stage.stack)) :
    stage.symbols (stage.set data value) = value := by
  cases stage <;> rfl

def CleanupStage.afterCfg (stage : CleanupStage) (tag : Tag)
    (data : TapeData) : machine.Cfg :=
  match stage with
  | .input => cleanupCfg .tagReverse tag (stage.cleared data)
  | .tagReverse => cleanupCfg .tags tag (stage.cleared data)
  | .tags => cleanupCfg .targetReverse tag (stage.cleared data)
  | .targetReverse => cleanupCfg .targets tag (stage.cleared data)
  | .targets => cleanupCfg .clauseCount tag (stage.cleared data)
  | .clauseCount => cleanupCfg .literalCount tag (stage.cleared data)
  | .literalCount => cleanupCfg .linkIndex tag (stage.cleared data)
  | .linkIndex => cleanupCfg .scratch tag (stage.cleared data)
  | .scratch => cleanupCfg .outputReverse tag (stage.cleared data)
  | .outputReverse => haltDataCfg initialTag (stage.cleared data)

def cleanedData (data : TapeData) : TapeData :=
  ⟨[], [], [], [], [], [], [], [], [], [], data.output⟩

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
