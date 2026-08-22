/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCleanupStageExecution

/-! # Grouped cleanup data for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def afterCleanupInput (data : TapeData) : TapeData :=
  { data with input := [] }

def afterCleanupTagReverse (data : TapeData) : TapeData :=
  { afterCleanupInput data with tagReverse := [] }

def afterCleanupTags (data : TapeData) : TapeData :=
  { afterCleanupTagReverse data with tags := [] }

def afterCleanupTargetReverse (data : TapeData) : TapeData :=
  { afterCleanupTags data with targetReverse := [] }

def streamCleanupData (data : TapeData) : TapeData :=
  { afterCleanupTargetReverse data with targets := [] }

def streamCleanupTime (data : TapeData) : Nat :=
  data.targets.length + 1 +
    (data.targetReverse.length + 1 +
      (data.tags.length + 1 +
        (data.tagReverse.length + 1 + (data.input.length + 1))))

def afterCleanupClauseCount (data : TapeData) : TapeData :=
  { data with clauseCount := [] }

def afterCleanupLiteralCount (data : TapeData) : TapeData :=
  { afterCleanupClauseCount data with literalCount := [] }

def afterCleanupLinkIndex (data : TapeData) : TapeData :=
  { afterCleanupLiteralCount data with linkIndex := [] }

def counterCleanupData (data : TapeData) : TapeData :=
  { afterCleanupLinkIndex data with scratch := [] }

def counterCleanupTime (data : TapeData) : Nat :=
  data.scratch.length + 1 +
    (data.linkIndex.length + 1 +
      (data.literalCount.length + 1 + (data.clauseCount.length + 1)))

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
