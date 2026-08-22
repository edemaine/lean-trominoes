/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordExecutionData

/-! # Tape projections of tagged cycle-link record execution data -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

@[simp] theorem afterCounterData_targets (data : TapeData)
    (counter : List Unit) :
    (afterCounterData data counter).targets = data.targets := by
  rfl

@[simp] theorem afterCounterData_scratch (data : TapeData)
    (counter : List Unit) :
    (afterCounterData data counter).scratch = [] := by
  rfl

@[simp] theorem closeOutputField_targets (data : TapeData) :
    (closeOutputField data).targets = data.targets := by
  rfl

@[simp] theorem closeOutputField_scratch (data : TapeData) :
    (closeOutputField data).scratch = data.scratch := by
  rfl

@[simp] theorem afterSourceVertexCounters_targets (data : TapeData) :
    (afterSourceVertexCounters data).targets = data.targets := by
  simp only [afterSourceVertexCounters,
    afterSourceVertexLiteralFirstCounter,
    afterSourceVertexClauseCounter, closeOutputField_targets,
    afterCounterData_targets]

@[simp] theorem afterSourceVertexCounters_scratch (data : TapeData) :
    (afterSourceVertexCounters data).scratch = [] := by
  simp only [afterSourceVertexCounters, closeOutputField_scratch,
    afterCounterData_scratch]

@[simp] theorem afterSourceEdgeCounters_targets (data : TapeData) :
    (afterSourceEdgeCounters data).targets = data.targets := by
  simp only [afterSourceEdgeCounters,
    afterSourceEdgeLiteralSecondCounter,
    afterSourceEdgeLiteralFirstCounter, closeOutputField_targets,
    afterCounterData_targets]

@[simp] theorem afterSourceEdgeCounters_scratch (data : TapeData) :
    (afterSourceEdgeCounters data).scratch = [] := by
  simp only [afterSourceEdgeCounters, closeOutputField_scratch,
    afterCounterData_scratch]

@[simp] theorem afterSourceEdgeIndexCounters_targets (data : TapeData) :
    (afterSourceEdgeIndexCounters data).targets = data.targets := by
  simp only [afterSourceEdgeIndexCounters,
    afterSourceEdgeIndexFirstCounter,
    afterSourceEdgeIndexLiteralCounter, closeOutputField_targets,
    afterCounterData_targets]

@[simp] theorem afterSourceEdgeIndexCounters_scratch (data : TapeData) :
    (afterSourceEdgeIndexCounters data).scratch = [] := by
  simp only [afterSourceEdgeIndexCounters, closeOutputField_scratch,
    afterCounterData_scratch]

@[simp] theorem afterSourceSourceCounters_targets (data : TapeData) :
    (afterSourceSourceCounters data).targets = data.targets := by
  simp only [afterSourceSourceCounters,
    afterSourceSourceClauseCounter,
    afterSourceSourceLiteralCounter, closeOutputField_targets,
    afterCounterData_targets]

@[simp] theorem afterSourceSourceCounters_scratch (data : TapeData) :
    (afterSourceSourceCounters data).scratch = [] := by
  simp only [afterSourceSourceCounters, closeOutputField_scratch,
    afterCounterData_scratch]

@[simp] theorem afterSourceCounters_targets (data : TapeData) :
    (afterSourceCounters data).targets = data.targets := by
  simp only [afterSourceCounters, afterSourceSourceCounters_targets,
    afterSourceEdgeIndexCounters_targets, afterSourceEdgeCounters_targets,
    afterSourceVertexCounters_targets]

@[simp] theorem afterSourceCounters_scratch (data : TapeData) :
    (afterSourceCounters data).scratch = [] := by
  simp only [afterSourceCounters, afterSourceSourceCounters_scratch]

@[simp] theorem beginSourceRecordData_targets (data : TapeData) :
    (beginSourceRecordData data).targets = data.targets := by
  rfl

@[simp] theorem afterSourcePrefixData_targets (data : TapeData) :
    (afterSourcePrefixData data).targets = data.targets := by
  simp only [afterSourcePrefixData, afterSourceCounters_targets,
    beginSourceRecordData_targets]

@[simp] theorem afterSourcePrefixData_scratch (data : TapeData) :
    (afterSourcePrefixData data).scratch = [] := by
  simp only [afterSourcePrefixData, afterSourceCounters_scratch]

@[simp] theorem afterFinishedSourceData_scratch (data : TapeData)
    (targetCount : Nat) (remainingTargets : List UnarySymbol) (tag : Tag) :
    (afterFinishedSourceData data targetCount remainingTargets tag).scratch =
      data.scratch := by
  rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
