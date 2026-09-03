/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseElementDegreeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanKindSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceParentClauseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyPermutation
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceOccurrences
import LeanTrominoes.PeriodicCNFStripHorizontalTypedVariableElementDegreeSemantics

/-! # Direct final variable-element degree semantics -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalVariableElementDegreeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance]
  directFinalClauseDegreePatternVariableDecidableEq
  horizontalThreeDMTripleVariableDecidableEq

private def variableElementDegreesOfKind
    (kind : PlanarThreeDM.VariableConnectorKind) : List Nat :=
  match kind with
  | .fixedRed => [2, 2, 2]
  | .fixedGreen | .fixedBlue => [2]

private def variableElementDegreesOfTernary (ternary : Bool) : List Nat :=
  if ternary = true then [2, 2, 2, 2, 2] else [2, 2, 2, 2]

private theorem flatMap_eq_of_forall₂
    {First Second Output : Type*}
    {relation : First → Second → Prop}
    {firsts : List First} {seconds : List Second}
    (firstBlock : First → List Output)
    (secondBlock : Second → List Output)
    (aligned : List.Forall₂ relation firsts seconds)
    (blocks : ∀ first second, relation first second →
      firstBlock first = secondBlock second) :
    firsts.flatMap firstBlock = seconds.flatMap secondBlock := by
  induction aligned with
  | nil => rfl
  | cons relation rest induction =>
      simp only [List.flatMap_cons, blocks _ _ relation, induction]

private theorem flatten_flatMap
    {First Second : Type*} (blocks : List (List First))
    (block : First → List Second) :
    blocks.flatten.flatMap block =
      blocks.flatMap fun values => values.flatMap block := by
  induction blocks with
  | nil => rfl
  | cons values blocks induction =>
      simp only [List.flatten_cons, List.flatMap_append,
        List.flatMap_cons, induction]

private theorem directSourceFinalVariableElementDegrees_eq_groupedData
    (symbols : List encoding.Γ) :
    directSourceFinalVariableElementDegrees decider symbols =
      (directSourceFinalGroupedOccurrenceData decider symbols).flatMap
        (fun data => variableElementDegreesOfKind data.kind) := by
  unfold directSourceFinalVariableElementDegrees
    FiniteUnaryFieldBlockMap.values
  have aligned :=
    directSourceFinalGroupedVariableFanSlotKinds decider symbols
  apply flatMap_eq_of_forall₂
    directSourceFinalVariableElementDegreeBlock
    (fun data => variableElementDegreesOfKind data.kind)
    aligned
  intro pair data relation
  unfold directSourceFinalVariableElementDegreeBlock
    variableElementDegreesOfKind
  rw [relation]
  rfl

private theorem directSourceFinalGroupedOccurrenceData_perm_compiled
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceData decider symbols).Perm
      (directSourceFinalCompiledOccurrenceData decider symbols) := by
  let keys := directSourceFinalOccurrenceCandidateKeys decider symbols
  let queries := directSourceFinalUniqueFanQueryKeys decider symbols
  let data := directSourceFinalCompiledOccurrenceData decider symbols
  let datum := FiniteAlphabetKeyedValueLookup.alignedDatum keys data
  have keysNodup : keys.Nodup :=
    directSourceFinalOccurrenceCandidateKeys_nodup decider symbols
  have keysDataLength : keys.length = data.length := by
    exact directSourceFinalOccurrenceCandidateKeys_length decider symbols
  have dataEq : data = keys.map datum := by
    exact FiniteAlphabetKeyedValueLookup.candidateValues_eq_map_alignedDatum
      keys data keysDataLength keysNodup
  rw [directSourceFinalGroupedOccurrenceData_eq_map_alignedDatum]
  change (queries.map datum).Perm data
  calc
    (queries.map datum).Perm (keys.map datum) :=
      (directSourceFinalUniqueFanQueryKeys_perm_candidateKeys
        decider symbols).map datum
    _ = data := dataEq.symm

private theorem finalClauseTerminalConnectorDegreeBlocks
    (fan : ClauseRibbonFanData) :
    (finalClauseTerminalConnectorKinds fan).flatMap
        variableElementDegreesOfKind =
      variableElementDegreesOfTernary fan.hasRight := by
  cases right : fan.hasRight <;>
    simp [finalClauseTerminalConnectorKinds,
      variableElementDegreesOfKind, variableElementDegreesOfTernary, right]

private theorem finalClauseFrameVariableDegreeBlock
    (block : List FinalClauseFrame)
    (kinds : block.map finalClauseFrameConnectorKind =
      finalClauseTerminalConnectorKinds (finalClauseFrameBlockFan block)) :
    block.flatMap (fun frame =>
        variableElementDegreesOfKind
          (finalClauseFrameConnectorKind frame)) =
      variableElementDegreesOfTernary
        (finalClauseFrameBlockFan block).hasRight := by
  calc
    _ = (block.map finalClauseFrameConnectorKind).flatMap
          variableElementDegreesOfKind := by
      rw [List.flatMap_map]
    _ = (finalClauseTerminalConnectorKinds
          (finalClauseFrameBlockFan block)).flatMap
            variableElementDegreesOfKind := by rw [kinds]
    _ = _ := finalClauseTerminalConnectorDegreeBlocks _

private theorem outputVariableDegrees_eq_outputClauseFans
    (descriptors : List PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    (HorizontalRoutedRouteHeaderClauseFrame.output descriptors).flatMap
        (fun frame => variableElementDegreesOfKind
          (finalClauseFrameConnectorKind frame)) =
      (HorizontalRoutedRouteHeaderClauseFrame.outputClauseFans
        descriptors).flatMap
          (fun fan => variableElementDegreesOfTernary fan.hasRight) := by
  rw [← HorizontalRoutedRouteHeaderClauseFrame.outputBlocks_flatten]
  rw [flatten_flatMap]
  unfold HorizontalRoutedRouteHeaderClauseFrame.outputClauseFans
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro block blockMember
  exact finalClauseFrameVariableDegreeBlock block
    (finalClauseFrameBlocks_spec descriptors block blockMember).2

private theorem directSourceFinalCompiledOccurrenceVariableDegrees_eq_clauseFans
    (symbols : List encoding.Γ) :
    (directSourceFinalCompiledOccurrenceData decider symbols).flatMap
        (fun data => variableElementDegreesOfKind data.kind) =
      (directSourceFinalClauseFans decider symbols).flatMap
        (fun fan => variableElementDegreesOfTernary fan.hasRight) := by
  rw [← directSourceFinalClauseFrames_map_occurrenceData]
  rw [List.flatMap_map]
  change
    (directSourceFinalClauseFrames decider symbols).flatMap
        (fun frame => variableElementDegreesOfKind
          (finalClauseFrameConnectorKind frame)) = _
  exact outputVariableDegrees_eq_outputClauseFans
    (directSourceFinalClauseDescriptors decider symbols)

private theorem directSourceFinalVariableElementDegrees_all_two
    (symbols : List encoding.Γ) :
    ∀ degree ∈ directSourceFinalVariableElementDegrees decider symbols,
      degree = 2 := by
  intro degree degreeMember
  unfold directSourceFinalVariableElementDegrees
    FiniteUnaryFieldBlockMap.values at degreeMember
  simp only [List.mem_flatMap] at degreeMember
  obtain ⟨pair, _pairMember, localMember⟩ := degreeMember
  cases kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) <;>
    simp [directSourceFinalVariableElementDegreeBlock, kindEq]
      at localMember <;>
    exact localMember

private theorem directSourceFinalClauseFanVariableDegrees_all_two
    (symbols : List encoding.Γ) :
    ∀ degree ∈ (directSourceFinalClauseFans decider symbols).flatMap
        (fun fan => variableElementDegreesOfTernary fan.hasRight),
      degree = 2 := by
  intro degree degreeMember
  simp only [List.mem_flatMap] at degreeMember
  obtain ⟨fan, _fanMember, localMember⟩ := degreeMember
  unfold variableElementDegreesOfTernary at localMember
  split at localMember <;> simp_all

private theorem directSourceFinalVariableElementDegrees_eq_clauseFans
    (symbols : List encoding.Γ) :
    directSourceFinalVariableElementDegrees decider symbols =
      (directSourceFinalClauseFans decider symbols).flatMap
        (fun fan => variableElementDegreesOfTernary fan.hasRight) := by
  have dataPerm :=
    directSourceFinalGroupedOccurrenceData_perm_compiled decider symbols
  have blockPerm := dataPerm.flatMap fun data _ => List.Perm.refl
    (variableElementDegreesOfKind data.kind)
  have lengthEq :
      (directSourceFinalVariableElementDegrees decider symbols).length =
        ((directSourceFinalClauseFans decider symbols).flatMap
          (fun fan => variableElementDegreesOfTernary fan.hasRight)).length := by
    rw [directSourceFinalVariableElementDegrees_eq_groupedData]
    exact blockPerm.length_eq.trans
      (congrArg List.length
        (directSourceFinalCompiledOccurrenceVariableDegrees_eq_clauseFans
          decider symbols))
  calc
    directSourceFinalVariableElementDegrees decider symbols =
        List.replicate
          (directSourceFinalVariableElementDegrees decider symbols).length 2 :=
      List.eq_replicate_length.mpr
        (directSourceFinalVariableElementDegrees_all_two decider symbols)
    _ = List.replicate
          ((directSourceFinalClauseFans decider symbols).flatMap
            (fun fan =>
              variableElementDegreesOfTernary fan.hasRight)).length 2 := by
      rw [lengthEq]
    _ = _ :=
      (List.eq_replicate_length.mpr
        (directSourceFinalClauseFanVariableDegrees_all_two
          decider symbols)).symm

/-- The directly compiled one-color variable degree prefix is exactly the
degree prefix of the typed horizontal 3DM source. -/
theorem directSourceFinalVariableElementDegrees_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalVariableElementDegrees decider symbols =
      horizontalTypedVariableElementDegrees
        (horizontalThreeDMTypedSourceComputed
          (PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  let source := PolySpaceCompiler.formulaOfSymbols decider symbols
  let typed := horizontalThreeDMTypedSourceComputed source
  have booleans :=
    directSourceFinalClauseFans_hasRight_eq_typedClauseTernary
      decider symbols
  have blocks := congrArg
    (List.flatMap variableElementDegreesOfTernary) booleans
  rw [directSourceFinalVariableElementDegrees_eq_clauseFans]
  rw [horizontalTypedVariableElementDegrees_eq_clauseFlatMap
    typed
    (horizontalThreeDMTypedSourceComputed_occurrencesAtMostThree source)
    (horizontalThreeDMTypedSourceComputed_arityTwoOrThree source)]
  simpa only [variableElementDegreesOfTernary,
    List.flatMap_map, Function.comp_def,
    decide_eq_true_eq] using blocks

end LeanTrominoes.PeriodicCNFStripReduction
