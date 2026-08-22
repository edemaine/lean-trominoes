/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceCountersExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetCountersExecution

/-! # One-link execution data for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def beginSourceRecordData (data : TapeData) : TapeData :=
  { data with outputReverse := .clauseMarker :: data.outputReverse }

def afterSourcePrefixData (data : TapeData) : TapeData :=
  afterSourceCounters (beginSourceRecordData data)

def afterSourceTargetData (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol) : TapeData :=
  { data with
    targets := remainingTargets
    outputReverse :=
      List.replicate targetCount .atomUnit ++ data.outputReverse }

def afterFinishedSourceData (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol) (tag : Tag) : TapeData :=
  let target := afterSourceTargetData data targetCount remainingTargets
  { target with
    outputReverse :=
      (sourceSuffix tag).reverse ++ .atomEnd :: target.outputReverse }

def beginTargetRecordData (data : TapeData) : TapeData :=
  { data with outputReverse := .clauseMarker :: data.outputReverse }

def afterTargetPrefixData (data : TapeData) : TapeData :=
  afterTargetCounters (beginTargetRecordData data)

def afterFinishedTargetData (data : TapeData) (tag : Tag) : TapeData :=
  { data with
    outputReverse :=
      (targetSuffix tag).reverse ++ .atomEnd :: data.outputReverse }

def afterIncrementLinkData (data : TapeData) : TapeData :=
  { data with linkIndex := () :: data.linkIndex }

def afterLinkData (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol) (tag : Tag) : TapeData :=
  afterIncrementLinkData
    (afterFinishedTargetData
      (afterTargetPrefixData
        (afterFinishedSourceData (afterSourcePrefixData data)
          targetCount remainingTargets tag))
      tag)

def sourcePrefixTime (data : TapeData) : Nat :=
  sourceCountersTime (beginSourceRecordData data) + 1

def sourceTargetTime (targetCount : Nat) : Nat :=
  1 + (targetCount + 1)

def targetRecordTime (data : TapeData) : Nat :=
  1 + (1 + (targetCountersTime (beginTargetRecordData data) + 1))

def linkTime (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol) (tag : Tag) : Nat :=
  targetRecordTime
      (afterFinishedSourceData (afterSourcePrefixData data)
        targetCount remainingTargets tag) +
    (sourceTargetTime targetCount + sourcePrefixTime data)

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
