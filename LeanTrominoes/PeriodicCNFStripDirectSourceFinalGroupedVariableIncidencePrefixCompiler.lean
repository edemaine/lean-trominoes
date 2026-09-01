/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalFiniteIncidenceDirectionQueryCompiler
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTyped
import LeanTrominoes.TM2CompositionMachine

/-! # Finite variable-incidence prefixes in stable identity order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open Gadget PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

noncomputable local instance directFinalGroupedVariablePrefixFanInhabited :
    Inhabited VariableRibbonFanData :=
  ⟨variableRibbonFanDataOfCode default⟩

/-- Recover the three meaningful variable-site slots from the generic
eight-slot role decoder.  Malformed larger slots use the harmless final-site
fallback. -/
def groupedVariableFanSiteSlot
    (slot : FiniteRoleSlotUnaryDecoder.Slot) : VariableSiteSlot :=
  match slot.val with
  | 0 => .first
  | 1 => .second
  | _ => .third

/-- Stable local triple order of the active occurrence module selected by a
grouped fan/slot pair. -/
def groupedVariableIncidenceTriples
    (pair : GroupedVariableFanSlot) : List VariableSiteTriple :=
  let slot := groupedVariableFanSiteSlot pair.2
  match pair.1.kind slot with
  | .fixedRed =>
      allFixedRedTriples.map fun triple => .fixedRed slot triple
  | .fixedGreen =>
      allOrdinaryTriples.map fun triple =>
        .ordinary slot .fixedGreen triple
  | .fixedBlue =>
      allOrdinaryTriples.map fun triple =>
        .ordinary slot .fixedBlue triple

/-- One finite variable-prefix query per local triple and color, in
triple-major and red/green/blue-minor order. -/
def groupedVariableIncidencePrefixQueryBlock
    (pair : GroupedVariableFanSlot) :
    List HorizontalFiniteIncidenceDirectionQuery :=
  (groupedVariableIncidenceTriples pair).flatMap fun triple =>
    [.variable pair.1 triple .red,
      .variable pair.1 triple .green,
      .variable pair.1 triple .blue]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedVariablePrefixStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Complete variable-incidence prefix-query stream, grouped by stable atom
identity, occurrence rank, local triple, and color. -/
def directSourceFinalGroupedVariableIncidencePrefixQueries
    (symbols : List encoding.Γ) :
    List HorizontalFiniteIncidenceDirectionQuery :=
  (directSourceFinalGroupedVariableFanSlots decider symbols).flatMap
    groupedVariableIncidencePrefixQueryBlock

/-- Independently delimited finite direction blocks selected by the grouped
variable-incidence prefix queries. -/
def directSourceFinalGroupedVariableIncidencePrefixDirectionTokens
    (symbols : List encoding.Γ) :
    List PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken :=
  HorizontalFiniteIncidenceDirectionQuery.delimitedOutput
    (directSourceFinalGroupedVariableIncidencePrefixQueries decider symbols)

/-- Finite block expansion compiles every local variable-incidence query in
polynomial time. -/
noncomputable def
    directSourceFinalGroupedVariableIncidencePrefixQueriesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableIncidencePrefixQueries decider) := by
  unfold directSourceFinalGroupedVariableIncidencePrefixQueries
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableFanSlotsComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      groupedVariableIncidencePrefixQueryBlock)

/-- The exact independently delimited finite prefix directions compile in
polynomial time. -/
noncomputable def
    directSourceFinalGroupedVariableIncidencePrefixDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableIncidencePrefixDirectionTokens
        decider) := by
  unfold directSourceFinalGroupedVariableIncidencePrefixDirectionTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableIncidencePrefixQueriesComputableInPolyTime
      decider)
    HorizontalFiniteIncidenceDirectionQuery.delimitedOutputComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
