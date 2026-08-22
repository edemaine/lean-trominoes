/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterMachine

/-! # Tape configurations for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

structure TapeData where
  input : List InputSymbol
  occurrenceReverse : List OccurrenceToken
  occurrences : List OccurrenceToken
  targetReverse : List UnarySymbol
  targets : List UnarySymbol
  clauseCount : List Unit
  literalCount : List Unit
  clauseIndex : List Unit
  edgeIndex : List Unit
  scratch : List Unit
  outputReverse : List OutputToken
  output : List OutputToken

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .occurrenceReverse => data.occurrenceReverse
  | .occurrences => data.occurrences
  | .targetReverse => data.targetReverse
  | .targets => data.targets
  | .clauseCount => data.clauseCount
  | .literalCount => data.literalCount
  | .clauseIndex => data.clauseIndex
  | .edgeIndex => data.edgeIndex
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) : machine.Cfg :=
  ⟨some label, state, tapes data⟩

def cursorCfg (label : Label) (cursor : Cursor) (data : TapeData) :
    machine.Cfg :=
  cfg label (.cursor cursor) data

def inputCfg (label : Label) (cursor : Cursor)
    (symbol : InputSymbol) (data : TapeData) : machine.Cfg :=
  cfg label (.input cursor (some symbol)) data

def occurrenceCfg (label : Label) (cursor : Cursor)
    (token : OccurrenceToken) (data : TapeData) : machine.Cfg :=
  cfg label (.occurrence cursor (some token)) data

def unaryCfg (label : Label) (cursor : Cursor)
    (symbol : UnarySymbol) (data : TapeData) : machine.Cfg :=
  cfg label (.unary cursor (some symbol)) data

def unitCfg (label : Label) (cursor : Cursor) (data : TapeData) :
    machine.Cfg :=
  cfg label (.unit cursor (some ())) data

def outputCfg (label : Label) (cursor : Cursor)
    (token : OutputToken) (data : TapeData) : machine.Cfg :=
  cfg label (.output cursor (some token)) data

def scanLeftCfg := cursorCfg .scanLeft
def pushOccurrenceCfg := inputCfg .pushOccurrence
def scanRightCfg := cursorCfg .scanRight
def pushTargetReverseCfg := inputCfg .pushTargetReverse
def restoreOccurrencesCfg := cursorCfg .restoreOccurrences
def pushOccurrenceForwardCfg := occurrenceCfg .pushOccurrenceForward
def restoreTargetsCfg := cursorCfg .restoreTargets
def pushTargetForwardCfg := unaryCfg .pushTargetForward
def scanOccurrencesCfg := cursorCfg .scanOccurrences
def beginRecordCfg := cursorCfg .beginRecord
def copyCounterCfg (stage : CounterStage) :=
  cursorCfg (.copyCounter stage)
def restoreCounterCfg (stage : CounterStage) :=
  cursorCfg (.restoreCounter stage)
def scanTargetCfg := cursorCfg .scanTarget
def finishRecordCfg (literalIndex : Fin 3)
    (currentNext anchorNext : Bool) :=
  cursorCfg (.finishRecord literalIndex currentNext anchorNext)
def reverseOutputCfg := cursorCfg .reverseOutput
def pushOutputCfg := outputCfg .pushOutput

def haltDataCfg (cursor : Cursor) (data : TapeData) : machine.Cfg :=
  ⟨none, .cursor cursor, tapes data⟩

def haltCfg (cursor : Cursor) (output : List OutputToken) : machine.Cfg :=
  haltDataCfg cursor ⟨[], [], [], [], [], [], [], [], [], [], [], output⟩

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
