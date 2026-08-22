/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterMachine

/-! # Tape configurations for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

structure TapeData where
  input : List InputSymbol
  tagReverse : List Tag
  tags : List Tag
  targetReverse : List UnarySymbol
  targets : List UnarySymbol
  clauseCount : List Unit
  literalCount : List Unit
  linkIndex : List Unit
  scratch : List Unit
  outputReverse : List OutputToken
  output : List OutputToken

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .tagReverse => data.tagReverse
  | .tags => data.tags
  | .targetReverse => data.targetReverse
  | .targets => data.targets
  | .clauseCount => data.clauseCount
  | .literalCount => data.literalCount
  | .linkIndex => data.linkIndex
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) : machine.Cfg :=
  ⟨some label, state, tapes data⟩

def cursorCfg (label : Label) (tag : Tag) (data : TapeData) : machine.Cfg :=
  cfg label (.cursor tag) data

def inputCfg (label : Label) (tag : Tag) (symbol : InputSymbol)
    (data : TapeData) : machine.Cfg :=
  cfg label (.input tag (some symbol)) data

def tagCfg (label : Label) (tag current : Tag) (data : TapeData) :
    machine.Cfg :=
  cfg label (.tag tag (some current)) data

def unaryCfg (label : Label) (tag : Tag) (symbol : UnarySymbol)
    (data : TapeData) : machine.Cfg :=
  cfg label (.unary tag (some symbol)) data

def unitCfg (label : Label) (tag : Tag) (data : TapeData) : machine.Cfg :=
  cfg label (.unit tag (some ())) data

def outputCfg (label : Label) (tag : Tag) (token : OutputToken)
    (data : TapeData) : machine.Cfg :=
  cfg label (.output tag (some token)) data

def scanHeaderCfg := cursorCfg .scanHeader
def pushClauseUnitCfg := inputCfg .pushClauseUnit
def pushTagReverseCfg := inputCfg .pushTagReverse
def scanTargetsInputCfg := cursorCfg .scanTargetsInput
def pushTargetReverseCfg := inputCfg .pushTargetReverse
def restoreTagsCfg := cursorCfg .restoreTags
def pushTagForwardCfg := tagCfg .pushTagForward
def restoreTargetsCfg := cursorCfg .restoreTargets
def pushTargetForwardCfg := unaryCfg .pushTargetForward
def scanLinksCfg := cursorCfg .scanLinks
def beginSourceRecordCfg := cursorCfg .beginSourceRecord
def copyCounterCfg (stage : CounterStage) := cursorCfg (.copyCounter stage)
def restoreCounterCfg (stage : CounterStage) :=
  cursorCfg (.restoreCounter stage)
def scanTargetCfg := cursorCfg .scanTarget
def finishSourceTargetCfg (tag : Tag) :=
  cursorCfg (.finishSourceTarget tag) tag
def beginTargetRecordCfg := cursorCfg .beginTargetRecord
def finishTargetRecordCfg (tag : Tag) :=
  cursorCfg (.finishTargetRecord tag) tag
def incrementLinkCfg := cursorCfg .incrementLink
def cleanupCfg (stage : CleanupStage) := cursorCfg (.cleanup stage)
def reverseOutputCfg := cursorCfg .reverseOutput
def pushOutputCfg := outputCfg .pushOutput

def haltDataCfg (tag : Tag) (data : TapeData) : machine.Cfg :=
  ⟨none, .cursor tag, tapes data⟩

def haltCfg (output : List OutputToken) : machine.Cfg :=
  haltDataCfg initialTag
    ⟨[], [], [], [], [], [], [], [], [], [], output⟩

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
