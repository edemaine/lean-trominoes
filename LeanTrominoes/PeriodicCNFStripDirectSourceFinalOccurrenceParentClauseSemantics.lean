/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFlatMapAligned
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFanCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalExpectedParentElementCodes
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedParentIndexSemantics

/-! # Actual-clause semantics of occurrence parent terminals -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM
open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.UnaryProgramClauseProfile

abbrev FinalClauseFrame :=
  HorizontalRoutedRouteHeaderClauseFrame.Data

/-- Occurrence data retained by one clause-local frame. -/
def finalClauseFrameOccurrenceData
    (frame : FinalClauseFrame) : FinalFanOccurrenceData :=
  HorizontalRoutedRouteHeader.occurrenceData frame.header

/-- Connector kind retained by one clause-local frame. -/
def finalClauseFrameConnectorKind
    (frame : FinalClauseFrame) : VariableConnectorKind :=
  (finalClauseFrameOccurrenceData frame).kind

/-- The common fan carried by a nonempty actual final-clause frame block. -/
abbrev finalClauseFrameBlockFan
    (block : List FinalClauseFrame) : ClauseRibbonFanData :=
  HorizontalRoutedRouteHeaderClauseFrame.blockFan block

/-- Connector kinds present at a binary or ternary final clause, in literal
order. -/
def finalClauseTerminalConnectorKinds
    (fan : ClauseRibbonFanData) : List VariableConnectorKind :=
  if fan.hasRight then [.fixedRed, .fixedBlue, .fixedGreen]
  else [.fixedRed, .fixedBlue]

@[simp] private theorem finalClauseFrameBlock_length
    (headers : List Header) :
    (HorizontalRoutedRouteHeaderClauseFrame.frameBlock headers).length =
      headers.length := by
  simp [HorizontalRoutedRouteHeaderClauseFrame.frameBlock]

private theorem finalClauseFrameBlockFan_frameBlock
    (headers : List Header) (positive : 0 < headers.length) :
    finalClauseFrameBlockFan
        (HorizontalRoutedRouteHeaderClauseFrame.frameBlock headers) =
      HorizontalRoutedRouteHeaderClauseFrame.clauseFanData headers := by
  cases headers with
  | nil => simp at positive
  | cons header headers =>
      simp [finalClauseFrameBlockFan,
        HorizontalRoutedRouteHeaderClauseFrame.blockFan,
        HorizontalRoutedRouteHeaderClauseFrame.frameBlock,
        HorizontalRoutedRouteHeaderClauseFrame.frameAt]

private theorem finalClauseFrameBlock_map_connectorKind
    (headers : List Header) :
    (HorizontalRoutedRouteHeaderClauseFrame.frameBlock headers).map
        finalClauseFrameConnectorKind =
      headers.map HorizontalRoutedRouteHeader.outputConnectorKind := by
  unfold finalClauseFrameConnectorKind finalClauseFrameOccurrenceData
  change
    (HorizontalRoutedRouteHeaderClauseFrame.frameBlock headers).map
        (HorizontalRoutedRouteHeader.outputConnectorKind ∘
          HorizontalRoutedRouteHeaderClauseFrame.Data.header) = _
  rw [← List.map_map,
    HorizontalRoutedRouteHeaderClauseFrame.frameBlock_map_header]

private theorem map_headerOf_outputConnectorKind
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor)
    (descriptors : List
      ClauseProfilePolarityRouteOperation.Descriptor) :
    (descriptors.map (headerOf prefixes)).map
        HorizontalRoutedRouteHeader.outputConnectorKind =
      descriptors.map
        HorizontalRoutedRouteHeader.descriptorOutputConnectorKind := by
  rw [List.map_map]
  apply List.map_congr_left
  intro descriptor _member
  rfl

private theorem routedClauseBlock_spec_of_arity
    (profile : ClauseProfile)
    (arity : profile.literals.length = 2 ∨
      profile.literals.length = 3) :
    ∀ routed ∈ clauseRouteBlocks profile,
      (routed.1.literals.length = 2 ∨
        routed.1.literals.length = 3) ∧
      routed.2.length = routed.1.literals.length ∧
      routed.2.map
          HorizontalRoutedRouteHeader.descriptorOutputConnectorKind =
        HorizontalRoutedRouteHeader.clauseConnectorKinds routed.1 := by
  cases profile <;> native_decide +revert

private theorem clauseConnectorKinds_eq_terminalKinds
    (profile : ClauseProfile)
    (arity : profile.literals.length = 2 ∨
      profile.literals.length = 3) :
    HorizontalRoutedRouteHeader.clauseConnectorKinds profile =
      if decide (3 ≤ profile.literals.length) then
        [.fixedRed, .fixedBlue, .fixedGreen]
      else [.fixedRed, .fixedBlue] := by
  cases profile <;> native_decide +revert

private theorem indexedFrames_no_clauseFans
    (allHeaders headers : List Header) (start : Nat)
    (positive : 0 < start) :
    ((headers.zipIdx start).map
      (HorizontalRoutedRouteHeaderClauseFrame.frameAt allHeaders)).flatMap
        finalClauseFanFrameBlock = [] := by
  induction headers generalizing start with
  | nil => rfl
  | cons header headers induction =>
      have groupNe :
          (HorizontalRoutedRouteHeaderClauseFrame.frameAt
            allHeaders (header, start)).group ≠ .top := by
        cases start with
        | zero => omega
        | succ offset =>
            cases offset <;>
              simp [HorizontalRoutedRouteHeaderClauseFrame.frameAt,
                terminalGroupOfLiteralIndex]
      rw [List.zipIdx_cons, List.map_cons, List.flatMap_cons]
      simp [finalClauseFanFrameBlock,
        HorizontalRoutedRouteHeaderClauseFrame.fanFrameBlock, groupNe,
        induction (start + 1) (by omega)]

private theorem finalClauseFrameBlock_clauseFans
    (headers : List Header) (positive : 0 < headers.length) :
    (HorizontalRoutedRouteHeaderClauseFrame.frameBlock headers).flatMap
        finalClauseFanFrameBlock =
      [HorizontalRoutedRouteHeaderClauseFrame.clauseFanData headers] := by
  cases headers with
  | nil => simp at positive
  | cons header headers =>
      unfold HorizontalRoutedRouteHeaderClauseFrame.frameBlock
      rw [List.zipIdx_cons, List.map_cons, List.flatMap_cons,
        indexedFrames_no_clauseFans (header :: headers) headers 1 (by omega)]
      simp [finalClauseFanFrameBlock,
        HorizontalRoutedRouteHeaderClauseFrame.fanFrameBlock,
        HorizontalRoutedRouteHeaderClauseFrame.frameAt,
        terminalGroupOfLiteralIndex]

private theorem clauseFrameBlocks_spec_of_arity
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor)
    (arity : profile.literals.length = 2 ∨
      profile.literals.length = 3) :
    ∀ block ∈
        HorizontalRoutedRouteHeaderClauseFrame.clauseFrameBlocks
          profile prefixes,
      0 < block.length ∧
        block.map finalClauseFrameConnectorKind =
          finalClauseTerminalConnectorKinds
            (finalClauseFrameBlockFan block) ∧
        block.flatMap finalClauseFanFrameBlock =
          [finalClauseFrameBlockFan block] := by
  intro block member
  unfold HorizontalRoutedRouteHeaderClauseFrame.clauseFrameBlocks
    HorizontalRoutedRouteHeaderClauseFrame.polarityHeaderBlocks at member
  rw [List.mem_map] at member
  obtain ⟨headers, headersMember, rfl⟩ := member
  rw [List.mem_map] at headersMember
  obtain ⟨routed, routedMember, rfl⟩ := headersMember
  let headers := routed.2.map (headerOf prefixes)
  have routedSpec :=
    routedClauseBlock_spec_of_arity profile arity routed routedMember
  have headersLength : headers.length = routed.1.literals.length := by
    simp [headers, routedSpec.2.1]
  have positive : 0 < headers.length := by
    rw [headersLength]
    omega
  constructor
  · simpa [headers] using positive
  constructor
  · rw [finalClauseFrameBlock_map_connectorKind,
      map_headerOf_outputConnectorKind, routedSpec.2.2]
    rw [finalClauseFrameBlockFan_frameBlock _ positive]
    simpa [finalClauseTerminalConnectorKinds,
      HorizontalRoutedRouteHeaderClauseFrame.clauseFanData,
      headersLength] using
        clauseConnectorKinds_eq_terminalKinds routed.1 routedSpec.1
  · rw [finalClauseFrameBlock_clauseFans _ positive,
      finalClauseFrameBlockFan_frameBlock _ positive]

private theorem figureClauseProfiles_arity_two_or_three
    (profile : DirectedClauseProfile) :
    ∀ generated ∈ figureClauseProfiles profile,
      generated.literals.length = 2 ∨
        generated.literals.length = 3 := by
  cases profile with
  | unary first direction =>
      simp only [figureClauseProfiles,
        FormulaShapeFigureNineRoutePrefix.clauseProfile]
      clear direction
      native_decide +revert
  | binary first firstDirection second secondDirection =>
      simp only [figureClauseProfiles,
        FormulaShapeFigureNineRoutePrefix.clauseProfile]
      clear firstDirection secondDirection
      native_decide +revert
  | ternary first firstDirection second secondDirection third thirdDirection =>
      simp only [figureClauseProfiles,
        FormulaShapeFigureNineRoutePrefix.clauseProfile]
      clear firstDirection secondDirection thirdDirection
      native_decide +revert

private theorem frameBlocks_spec
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor)
    (arities : ∀ profile ∈ profiles,
      profile.literals.length = 2 ∨
        profile.literals.length = 3) :
    ∀ block ∈ HorizontalRoutedRouteHeaderClauseFrame.frameBlocks
        profiles prefixes,
      0 < block.length ∧
        block.map finalClauseFrameConnectorKind =
          finalClauseTerminalConnectorKinds
            (finalClauseFrameBlockFan block) ∧
        block.flatMap finalClauseFanFrameBlock =
          [finalClauseFrameBlockFan block] := by
  induction profiles generalizing prefixes with
  | nil => simp [HorizontalRoutedRouteHeaderClauseFrame.frameBlocks]
  | cons profile profiles induction =>
      intro block member
      simp only [HorizontalRoutedRouteHeaderClauseFrame.frameBlocks,
        List.mem_append] at member
      rcases member with member | member
      · exact clauseFrameBlocks_spec_of_arity profile _
          (arities profile (by simp)) block member
      · have tailArities : ∀ later ∈ profiles,
            later.literals.length = 2 ∨
              later.literals.length = 3 := by
          intro later laterMember
          exact arities later (by simp [laterMember])
        exact induction (prefixes.drop profile.literals.length)
          tailArities block member

/-- Every boundary-preserving finite descriptor block is nonempty and its
retained occurrence kinds are exactly the terminals selected by its fan. -/
theorem tokenFinalClauseFrameBlocks_spec (token : Token) :
    ∀ block ∈ HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token,
      0 < block.length ∧
        block.map finalClauseFrameConnectorKind =
          finalClauseTerminalConnectorKinds
            (finalClauseFrameBlockFan block) ∧
        block.flatMap finalClauseFanFrameBlock =
          [finalClauseFrameBlockFan block] := by
  cases token with
  | «variable» => simp [HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks]
  | clause profile =>
      unfold HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks
        HorizontalRoutedRouteHeaderClauseFrame.sourceClauseFrameBlocks
      exact frameBlocks_spec _ _
        (figureClauseProfiles_arity_two_or_three
          (orderedDirectedProfile profile))

private theorem finalClauseFrameBlocks_clauseFans_eq_map
    (blocks : List (List FinalClauseFrame))
    (spec : ∀ block ∈ blocks,
      block.flatMap finalClauseFanFrameBlock =
        [finalClauseFrameBlockFan block]) :
    blocks.flatten.flatMap finalClauseFanFrameBlock =
      blocks.map finalClauseFrameBlockFan := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      have blockSpec := spec block (by simp)
      have tailSpec : ∀ later ∈ blocks,
          later.flatMap finalClauseFanFrameBlock =
            [finalClauseFrameBlockFan later] := by
        intro later member
        exact spec later (by simp [member])
      rw [List.flatten_cons, List.flatMap_append, List.map_cons,
        blockSpec]
      exact congrArg (List.cons (finalClauseFrameBlockFan block))
        (induction tailSpec)

/-- Selecting `.top` frames from one descriptor yields exactly the common
fan of each retained actual-clause block. -/
theorem tokenFinalClauseFans_eq_map_blockFan (token : Token) :
    (HorizontalRoutedRouteHeaderClauseFrame.tokenBlock token).flatMap
        finalClauseFanFrameBlock =
      (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token).map
        finalClauseFrameBlockFan := by
  rw [← HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks_flatten]
  apply finalClauseFrameBlocks_clauseFans_eq_map
  intro block member
  exact (tokenFinalClauseFrameBlocks_spec token block member).2.2

theorem finalClauseFrameBlocks_spec (source : List Token) :
    ∀ block ∈ HorizontalRoutedRouteHeaderClauseFrame.outputBlocks source,
      0 < block.length ∧
        block.map finalClauseFrameConnectorKind =
          finalClauseTerminalConnectorKinds
            (finalClauseFrameBlockFan block) := by
  intro block member
  unfold HorizontalRoutedRouteHeaderClauseFrame.outputBlocks at member
  rw [List.mem_flatMap] at member
  obtain ⟨token, _tokenMember, blockMember⟩ := member
  have spec := tokenFinalClauseFrameBlocks_spec token block blockMember
  exact ⟨spec.1, spec.2.1⟩

/-- Globally, the actual final-clause fan stream is the fan projection of
the boundary-preserving frame blocks. -/
theorem finalClauseFans_eq_map_blockFan (source : List Token) :
    (HorizontalRoutedRouteHeaderClauseFrame.output source).flatMap
        finalClauseFanFrameBlock =
      (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks source).map
        finalClauseFrameBlockFan := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      change
        (HorizontalRoutedRouteHeaderClauseFrame.tokenBlock token ++
          HorizontalRoutedRouteHeaderClauseFrame.output source).flatMap
            finalClauseFanFrameBlock =
          (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token ++
            HorizontalRoutedRouteHeaderClauseFrame.outputBlocks source).map
              finalClauseFrameBlockFan
      rw [List.flatMap_append, List.map_append,
        tokenFinalClauseFans_eq_map_blockFan, induction]

/-- One occurrence-derived RGB terminal block at every terminal present in
an actual final clause. -/
def finalClauseOccurrenceTerminalElementCodeBlock
    (index : Nat) (fan : ClauseRibbonFanData) : List Nat :=
  (finalClauseTerminalConnectorKinds fan).flatMap fun kind =>
    finalConnectorParentElementCodeBlock kind index

private theorem zipWith_frameData_replicate
    (block : List FinalClauseFrame) (index : Nat) :
    List.zipWith finalOccurrenceParentElementCodeBlock
        (block.map finalClauseFrameOccurrenceData)
        (List.replicate block.length index) =
      block.map fun frame =>
        finalConnectorParentElementCodeBlock
          (finalClauseFrameOccurrenceData frame).kind index := by
  induction block with
  | nil => rfl
  | cons frame block induction =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, finalOccurrenceParentElementCodeBlock]
      rw [induction]

private theorem zipWith_frameBlock_replicate
    (block : List FinalClauseFrame) (index : Nat)
    (kinds : block.map finalClauseFrameConnectorKind =
      finalClauseTerminalConnectorKinds
        (finalClauseFrameBlockFan block)) :
    (List.zipWith finalOccurrenceParentElementCodeBlock
        (block.map finalClauseFrameOccurrenceData)
        (List.replicate block.length index)).flatten =
      finalClauseOccurrenceTerminalElementCodeBlock index
        (finalClauseFrameBlockFan block) := by
  rw [zipWith_frameData_replicate]
  unfold finalClauseOccurrenceTerminalElementCodeBlock
  have expanded := congrArg
    (List.flatMap fun kind =>
      finalConnectorParentElementCodeBlock kind index) kinds
  simpa [List.flatten_eq_flatMap, List.flatMap_map,
    Function.comp_def, finalClauseFrameConnectorKind] using expanded

private theorem occurrenceParentCodes_expectedAux_eq_zipIdx
    (start : Nat) (blocks : List (List FinalClauseFrame))
    (spec : ∀ block ∈ blocks,
      0 < block.length ∧
        block.map finalClauseFrameConnectorKind =
          finalClauseTerminalConnectorKinds
            (finalClauseFrameBlockFan block)) :
    (List.zipWith finalOccurrenceParentElementCodeBlock
        (blocks.flatMap fun block =>
          block.map finalClauseFrameOccurrenceData)
        (FiniteBlockIndices.expectedAux List.length start blocks)).flatten =
      (blocks.zipIdx start).flatMap fun tagged =>
        finalClauseOccurrenceTerminalElementCodeBlock tagged.2
          (finalClauseFrameBlockFan tagged.1) := by
  induction blocks generalizing start with
  | nil => rfl
  | cons block blocks induction =>
      have blockSpec := spec block (by simp)
      have tailSpec : ∀ later ∈ blocks,
          0 < later.length ∧
            later.map finalClauseFrameConnectorKind =
              finalClauseTerminalConnectorKinds
                (finalClauseFrameBlockFan later) := by
        intro later member
        exact spec later (by simp [member])
      have nextEq :
          FiniteBlockIndices.nextIndex start block.length = start + 1 := by
        simp [FiniteBlockIndices.nextIndex,
          Nat.ne_of_gt blockSpec.1]
      simp only [List.flatMap_cons, FiniteBlockIndices.expectedAux,
        List.zipIdx_cons, List.flatMap_cons]
      rw [List.zipWith_append_of_length_eq
        finalOccurrenceParentElementCodeBlock
        (block.map finalClauseFrameOccurrenceData)
        (blocks.flatMap fun later =>
          later.map finalClauseFrameOccurrenceData)
        (List.replicate block.length start)
        (FiniteBlockIndices.expectedAux List.length
          (FiniteBlockIndices.nextIndex start block.length) blocks)
        (by simp),
        List.flatten_append,
        zipWith_frameBlock_replicate block start blockSpec.2,
        nextEq,
        induction (start + 1) tailSpec]

private theorem zipIdx_terminalBlocks_eq_zipWith_range
    (start : Nat) (blocks : List (List FinalClauseFrame)) :
    ((blocks.zipIdx start).flatMap fun tagged =>
        finalClauseOccurrenceTerminalElementCodeBlock tagged.2
          (finalClauseFrameBlockFan tagged.1)) =
      (List.zipWith finalClauseOccurrenceTerminalElementCodeBlock
        (List.range' start blocks.length)
        (blocks.map finalClauseFrameBlockFan)).flatten := by
  induction blocks generalizing start with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.zipIdx_cons, List.flatMap_cons, List.length_cons,
        List.range'_succ, List.map_cons, List.zipWith_cons_cons,
        List.flatten_cons]
      rw [induction (start + 1)]

private theorem occurrenceParentElementCodes_eq_clauseBlocks_of_spec
    (blocks : List (List FinalClauseFrame))
    (spec : ∀ block ∈ blocks,
      0 < block.length ∧
        block.map finalClauseFrameConnectorKind =
          finalClauseTerminalConnectorKinds
            (finalClauseFrameBlockFan block)) :
    (List.zipWith finalOccurrenceParentElementCodeBlock
        (blocks.flatten.map finalClauseFrameOccurrenceData)
        (FiniteBlockIndices.expected List.length blocks)).flatten =
      (List.zipWith finalClauseOccurrenceTerminalElementCodeBlock
        (List.range (blocks.map finalClauseFrameBlockFan).length)
        (blocks.map finalClauseFrameBlockFan)).flatten := by
  rw [show blocks.flatten.map finalClauseFrameOccurrenceData =
      blocks.flatMap (fun block =>
        block.map finalClauseFrameOccurrenceData) by
    rw [List.map_flatten]
    clear spec
    induction blocks with
    | nil => rfl
    | cons block blocks induction =>
        simp only [List.map_cons, List.flatten_cons, List.flatMap_cons,
          induction]]
  rw [show FiniteBlockIndices.expected List.length blocks =
      FiniteBlockIndices.expectedAux List.length 0 blocks by rfl]
  rw [occurrenceParentCodes_expectedAux_eq_zipIdx 0 blocks spec,
    zipIdx_terminalBlocks_eq_zipWith_range]
  simp only [List.length_map, List.range_eq_range']

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem directSourceFinalClauseFrames_eq_outputBlocks_flatten
    (symbols : List encoding.Γ) :
    directSourceFinalClauseFrames decider symbols =
      (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
        (directSourceFinalClauseDescriptors decider symbols)).flatten := by
  unfold directSourceFinalClauseFrames
  exact
    (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks_flatten _).symm

private theorem directSourceFinalOccurrenceParentElementCodes_eq_blockFans
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceParentElementCodes decider symbols =
      (List.zipWith finalClauseOccurrenceTerminalElementCodeBlock
        (List.range
          ((HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
            (directSourceFinalClauseDescriptors decider symbols)).map
              finalClauseFrameBlockFan).length)
        ((HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
          (directSourceFinalClauseDescriptors decider symbols)).map
            finalClauseFrameBlockFan)).flatten := by
  let blocks := HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
    (directSourceFinalClauseDescriptors decider symbols)
  unfold directSourceFinalOccurrenceParentElementCodes
  rw [← directSourceFinalClauseFrames_map_occurrenceData]
  rw [directSourceFinalClauseFrames_eq_outputBlocks_flatten]
  rw [directSourceFinalOccurrenceParentIndices_eq_expected]
  exact occurrenceParentElementCodes_eq_clauseBlocks_of_spec blocks
    (finalClauseFrameBlocks_spec
      (directSourceFinalClauseDescriptors decider symbols))

/-- The occurrence-derived parent-terminal stream is exactly one RGB block
for every present terminal of every actual final clause, indexed by the same
clause ordinal used by canonical clause elements. -/
theorem directSourceFinalOccurrenceParentElementCodes_eq_clauseBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceParentElementCodes decider symbols =
      (List.zipWith finalClauseOccurrenceTerminalElementCodeBlock
        (List.range (directSourceFinalClauseFans decider symbols).length)
        (directSourceFinalClauseFans decider symbols)).flatten := by
  rw [directSourceFinalClauseFans_eq_blockFans]
  exact directSourceFinalOccurrenceParentElementCodes_eq_blockFans
    decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
