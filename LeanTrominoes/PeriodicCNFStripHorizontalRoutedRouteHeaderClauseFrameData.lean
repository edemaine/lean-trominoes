/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceBlockCompiler
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseRibbonFanDataEncoding

/-! # Clause-local finite frames for routed Figure 9 headers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderClauseFrame

open Computability Turing
open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- The finite clause-side data aligned with one final routed occurrence.
Retaining the header makes the presentation-order contract explicit. -/
structure Data where
  header : Header
  clauseFan : ClauseRibbonFanData
  group : X3CClauseTerminalGroup
  deriving DecidableEq, Fintype

private def defaultClauseFan : ClauseRibbonFanData where
  hasRight := false
  direction := fun _ => .north

instance : Inhabited Data :=
  ⟨⟨default, defaultClauseFan, .top⟩⟩

/-- Stored routes run from clause to variable; occurrence routes arrive at
the clause in the opposite direction. Missing terminals use north. -/
def directionAt (headers : List Header) (index : Nat) : AxisDirection :=
  (headers[index]?).map
    (fun header => (HorizontalRoutedRouteHeader.outputFirstDirection header).opposite)
    |>.getD .north

/-- Assemble the finite clause fan carried by one consecutive final-clause
header block. -/
def clauseFanData (headers : List Header) : ClauseRibbonFanData where
  hasRight := decide (3 ≤ headers.length)
  direction
    | .top => directionAt headers 0
    | .left => directionAt headers 1
    | .right => directionAt headers 2

/-- Attach the common clause fan and literal-position terminal group to one
indexed header. -/
def frameAt (headers : List Header) (indexed : Header × Nat) : Data :=
  ⟨indexed.1, clauseFanData headers,
    terminalGroupOfLiteralIndex indexed.2⟩

/-- Attach one common clause fan and the literal-position terminal group to
every header of a final clause. -/
def frameBlock (headers : List Header) : List Data :=
  headers.zipIdx.map (frameAt headers)

@[simp] theorem frameBlock_map_header (headers : List Header) :
    (frameBlock headers).map Data.header = headers := by
  unfold frameBlock
  rw [List.map_map]
  change headers.zipIdx.map Prod.fst = headers
  exact List.zipIdx_map_fst 0 headers

/-- Final-clause header blocks generated from one pre-polarity Figure 9
clause and its aligned finite source-prefix descriptors. -/
def polarityHeaderBlocks
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    List (List Header) :=
  (clauseRouteBlocks profile).map fun block =>
    block.2.map (headerOf prefixes)

/-- Clause-local frames for every polarity-normalized clause generated from
one Figure 9 clause. -/
def clauseFrames
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    List Data :=
  (polarityHeaderBlocks profile prefixes).flatMap frameBlock

/-- The same final-clause frames with the actual clause boundaries retained. -/
def clauseFrameBlocks
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    List (List Data) :=
  (polarityHeaderBlocks profile prefixes).map frameBlock

@[simp] theorem clauseFrameBlocks_flatten
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    (clauseFrameBlocks profile prefixes).flatten =
      clauseFrames profile prefixes := by
  unfold clauseFrameBlocks clauseFrames
  rw [List.flatten_eq_flatMap, List.flatMap_map]
  simp only [id_eq]

theorem polarityHeaderBlocks_flatten
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    (polarityHeaderBlocks profile prefixes).flatten =
      clauseHeaders profile prefixes := by
  change
    ((clauseRouteBlocks profile).map fun block =>
        block.2.map (headerOf prefixes)).flatten =
      ((clauseRouteBlocks profile).flatMap Prod.snd).map
        (headerOf prefixes)
  rw [List.flatten_eq_flatMap, List.flatMap_map, List.map_flatMap]
  rfl

@[simp] theorem clauseFrames_map_header
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    (clauseFrames profile prefixes).map Data.header =
      clauseHeaders profile prefixes := by
  unfold clauseFrames
  rw [List.map_flatMap]
  simp only [frameBlock_map_header]
  rw [← polarityHeaderBlocks_flatten profile prefixes]
  rw [List.flatten_eq_flatMap]
  apply List.flatMap_congr
  intro block blockMember
  rfl

/-- Consume one source-prefix block per Figure 9 clause while retaining the
same clause-local framing boundaries used above. -/
def frames : List ClauseProfile →
    List HorizontalRoutedRouteHeader.PrefixDescriptor → List Data
  | [], _ => []
  | profile :: profiles, prefixes =>
      let count := profile.literals.length
      clauseFrames profile (prefixes.take count) ++
        frames profiles (prefixes.drop count)

/-- Clause-boundary-preserving version of `frames`. -/
def frameBlocks : List ClauseProfile →
    List HorizontalRoutedRouteHeader.PrefixDescriptor → List (List Data)
  | [], _ => []
  | profile :: profiles, prefixes =>
      let count := profile.literals.length
      clauseFrameBlocks profile (prefixes.take count) ++
        frameBlocks profiles (prefixes.drop count)

@[simp] theorem frameBlocks_flatten
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    (frameBlocks profiles prefixes).flatten =
      frames profiles prefixes := by
  induction profiles generalizing prefixes with
  | nil => rfl
  | cons profile profiles induction =>
      simp only [frameBlocks, frames, List.flatten_append,
        clauseFrameBlocks_flatten, induction]

@[simp] theorem frames_map_header
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    (frames profiles prefixes).map Data.header =
      headers profiles prefixes := by
  induction profiles generalizing prefixes with
  | nil => rfl
  | cons profile profiles induction =>
      simp only [frames, headers, List.map_append,
        clauseFrames_map_header, induction]

/-- Clause-local frames after applying the final clockwise permutation to
each Figure 9 clause profile and its aligned prefix block. -/
def finalFrames : List ClauseProfile →
    List HorizontalRoutedRouteHeader.PrefixDescriptor → List Data
  | [], _ => []
  | profile :: profiles, prefixes =>
      let count := profile.literals.length
      clauseFrames (reorderProfile profile)
          (reorderList (prefixes.take count)) ++
        finalFrames profiles (prefixes.drop count)

/-- Boundary-preserving final-clockwise frame blocks. -/
def finalFrameBlocks : List ClauseProfile →
    List HorizontalRoutedRouteHeader.PrefixDescriptor → List (List Data)
  | [], _ => []
  | profile :: profiles, prefixes =>
      let count := profile.literals.length
      clauseFrameBlocks (reorderProfile profile)
          (reorderList (prefixes.take count)) ++
        finalFrameBlocks profiles (prefixes.drop count)

@[simp] theorem finalFrameBlocks_flatten
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    (finalFrameBlocks profiles prefixes).flatten =
      finalFrames profiles prefixes := by
  induction profiles generalizing prefixes with
  | nil => rfl
  | cons profile profiles induction =>
      simp only [finalFrameBlocks, finalFrames, List.flatten_append,
        clauseFrameBlocks_flatten, induction]

@[simp] theorem finalFrames_map_header
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    (finalFrames profiles prefixes).map Data.header =
      finalHeaders profiles prefixes := by
  induction profiles generalizing prefixes with
  | nil => rfl
  | cons profile profiles induction =>
      simp only [finalFrames, finalHeaders, List.map_append,
        clauseFrames_map_header, induction]

/-- Complete clause-local frame stream generated by one directed parent
clause profile. -/
def sourceClauseFrames (profile : DirectedClauseProfile) : List Data :=
  let ordered := orderedDirectedProfile profile
  finalFrames (figureClauseProfiles ordered)
    (FormulaShapeFigureNineRoutePrefix.clauseDescriptors ordered)

/-- Actual final-clause frame blocks generated by one directed descriptor. -/
def sourceClauseFrameBlocks
    (profile : DirectedClauseProfile) : List (List Data) :=
  let ordered := orderedDirectedProfile profile
  finalFrameBlocks (figureClauseProfiles ordered)
    (FormulaShapeFigureNineRoutePrefix.clauseDescriptors ordered)

@[simp] theorem sourceClauseFrameBlocks_flatten
    (profile : DirectedClauseProfile) :
    (sourceClauseFrameBlocks profile).flatten =
      sourceClauseFrames profile := by
  simp [sourceClauseFrameBlocks, sourceClauseFrames]

@[simp] theorem sourceClauseFrames_map_header
    (profile : DirectedClauseProfile) :
    (sourceClauseFrames profile).map Data.header =
      sourceClauseHeaders profile := by
  simp [sourceClauseFrames, sourceClauseHeaders]

/-- Variable markers generate no headers; parent clauses expand to their
complete final occurrence-frame blocks. -/
def tokenBlock : FormulaShapeDirectionOrdering.Token → List Data
  | .clause profile => sourceClauseFrames profile
  | .variable => []

/-- Actual final-clause frame blocks generated by one finite source token. -/
def tokenBlocks :
    FormulaShapeDirectionOrdering.Token → List (List Data)
  | .clause profile => sourceClauseFrameBlocks profile
  | .variable => []

/-- The common clause fan retained by one nonempty actual-clause block. -/
def blockFan (block : List Data) : ClauseRibbonFanData :=
  (block.headD default).clauseFan

/-- Select the one fan carried by a clause-start frame. -/
def fanFrameBlock (frame : Data) : List ClauseRibbonFanData :=
  if frame.group = .top then [frame.clauseFan] else []

/-- One actual final-clause fan per boundary-preserving token block. -/
def tokenClauseFans
    (token : FormulaShapeDirectionOrdering.Token) :
    List ClauseRibbonFanData :=
  (tokenBlocks token).map blockFan

@[simp] theorem tokenBlocks_flatten
    (token : FormulaShapeDirectionOrdering.Token) :
    (tokenBlocks token).flatten = tokenBlock token := by
  cases token with
  | clause profile => exact sourceClauseFrameBlocks_flatten profile
  | «variable» => rfl

@[simp] theorem tokenBlock_map_header
    (token : FormulaShapeDirectionOrdering.Token) :
    (tokenBlock token).map Data.header =
      FormulaShapeFigureNinePolarityRouteHeader.tokenBlock token := by
  cases token with
  | clause profile => exact sourceClauseFrames_map_header profile
  | «variable» => rfl

/-- Complete clause-local finite frame column in final occurrence order. -/
def output (source : List FormulaShapeDirectionOrdering.Token) : List Data :=
  source.flatMap tokenBlock

/-- All actual final-clause frame blocks, retaining boundaries globally. -/
def outputBlocks
    (source : List FormulaShapeDirectionOrdering.Token) : List (List Data) :=
  source.flatMap tokenBlocks

/-- One clause fan per actual boundary-preserving clause block. -/
def outputClauseFans
    (source : List FormulaShapeDirectionOrdering.Token) :
    List ClauseRibbonFanData :=
  (outputBlocks source).map blockFan

@[simp] theorem outputBlocks_flatten
    (source : List FormulaShapeDirectionOrdering.Token) :
    (outputBlocks source).flatten = output source := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      change (tokenBlocks token ++ outputBlocks source).flatten =
        tokenBlock token ++ output source
      rw [List.flatten_append, tokenBlocks_flatten, induction]

private theorem indexedFrames_no_fans
    (allHeaders headers : List Header) (start : Nat)
    (positive : 0 < start) :
    ((headers.zipIdx start).map (frameAt allHeaders)).flatMap
        fanFrameBlock = [] := by
  induction headers generalizing start with
  | nil => rfl
  | cons header headers induction =>
      have groupNe : (frameAt allHeaders (header, start)).group ≠ .top := by
        cases start with
        | zero => omega
        | succ offset =>
            cases offset <;> simp [frameAt, terminalGroupOfLiteralIndex]
      rw [List.zipIdx_cons, List.map_cons, List.flatMap_cons]
      simp [fanFrameBlock, groupNe,
        induction (start + 1) (by omega)]

private theorem frameBlock_fans
    (headers : List Header) (positive : 0 < headers.length) :
    (frameBlock headers).flatMap fanFrameBlock =
      [clauseFanData headers] := by
  cases headers with
  | nil => simp at positive
  | cons header headers =>
      unfold frameBlock
      rw [List.zipIdx_cons, List.map_cons, List.flatMap_cons,
        indexedFrames_no_fans (header :: headers) headers 1 (by omega)]
      simp [fanFrameBlock, frameAt, terminalGroupOfLiteralIndex]

private theorem blockFan_frameBlock
    (headers : List Header) (positive : 0 < headers.length) :
    blockFan (frameBlock headers) = clauseFanData headers := by
  cases headers with
  | nil => simp at positive
  | cons header headers =>
      simp [blockFan, frameBlock, frameAt]

private theorem routeBlock_nonempty (profile : ClauseProfile) :
    ∀ routed ∈ clauseRouteBlocks profile, 0 < routed.2.length := by
  cases profile <;> native_decide +revert

private theorem clauseFrameBlocks_fan_spec
    (profile : ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    ∀ block ∈ clauseFrameBlocks profile prefixes,
      block.flatMap fanFrameBlock = [blockFan block] := by
  intro block member
  unfold clauseFrameBlocks polarityHeaderBlocks at member
  rw [List.mem_map] at member
  obtain ⟨headers, headersMember, rfl⟩ := member
  rw [List.mem_map] at headersMember
  obtain ⟨routed, routedMember, rfl⟩ := headersMember
  have positive : 0 <
      (routed.2.map (headerOf prefixes)).length := by
    simpa using routeBlock_nonempty profile routed routedMember
  rw [frameBlock_fans _ positive, blockFan_frameBlock _ positive]

private theorem frameBlocks_fan_spec
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    ∀ block ∈ frameBlocks profiles prefixes,
      block.flatMap fanFrameBlock = [blockFan block] := by
  induction profiles generalizing prefixes with
  | nil => simp [frameBlocks]
  | cons profile profiles induction =>
      intro block member
      simp only [frameBlocks, List.mem_append] at member
      rcases member with member | member
      · exact clauseFrameBlocks_fan_spec profile _ block member
      · exact induction _ block member

private theorem finalFrameBlocks_fan_spec
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    ∀ block ∈ finalFrameBlocks profiles prefixes,
      block.flatMap fanFrameBlock = [blockFan block] := by
  induction profiles generalizing prefixes with
  | nil => simp [finalFrameBlocks]
  | cons profile profiles induction =>
      intro block member
      simp only [finalFrameBlocks, List.mem_append] at member
      rcases member with member | member
      · exact clauseFrameBlocks_fan_spec (reorderProfile profile) _ block member
      · exact induction _ block member

private theorem tokenBlocks_fan_spec
    (token : FormulaShapeDirectionOrdering.Token) :
    ∀ block ∈ tokenBlocks token,
      block.flatMap fanFrameBlock = [blockFan block] := by
  cases token with
  | «variable» => simp [tokenBlocks]
  | clause profile =>
      exact finalFrameBlocks_fan_spec _ _

private theorem outputBlocks_fan_spec
    (source : List FormulaShapeDirectionOrdering.Token) :
    ∀ block ∈ outputBlocks source,
      block.flatMap fanFrameBlock = [blockFan block] := by
  intro block member
  unfold outputBlocks at member
  rw [List.mem_flatMap] at member
  obtain ⟨token, _tokenMember, blockMember⟩ := member
  exact tokenBlocks_fan_spec token block blockMember

private theorem flatten_fans_eq_map
    (blocks : List (List Data))
    (spec : ∀ block ∈ blocks,
      block.flatMap fanFrameBlock = [blockFan block]) :
    blocks.flatten.flatMap fanFrameBlock = blocks.map blockFan := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      have blockSpec := spec block (by simp)
      have tailSpec : ∀ later ∈ blocks,
          later.flatMap fanFrameBlock = [blockFan later] := by
        intro later member
        exact spec later (by simp [member])
      rw [List.flatten_cons, List.flatMap_append, List.map_cons,
        blockSpec]
      exact congrArg (List.cons (blockFan block)) (induction tailSpec)

/-- Selecting the `.top` frame fan from the flattened occurrence stream is
exactly the direct fan projection of the retained actual-clause blocks. -/
theorem output_flatMap_fanFrameBlock_eq_outputClauseFans
    (source : List FormulaShapeDirectionOrdering.Token) :
    (output source).flatMap fanFrameBlock = outputClauseFans source := by
  rw [← outputBlocks_flatten]
  exact flatten_fans_eq_map _ (outputBlocks_fan_spec source)

@[simp] theorem output_map_header
    (source : List FormulaShapeDirectionOrdering.Token) :
    (output source).map Data.header =
      FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders source := by
  unfold output
    FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro token tokenMember
  exact tokenBlock_map_header token

/-- Forgetting the clause-local additions and projecting the retained headers
recovers the established flat occurrence-data stream. -/
theorem output_map_occurrenceData
    (source : List FormulaShapeDirectionOrdering.Token) :
    (output source).map
        (HorizontalRoutedRouteHeader.occurrenceData ∘ Data.header) =
      HorizontalRoutedRouteHeaderOccurrenceBlock.output source := by
  rw [← List.map_map, output_map_header]
  unfold FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders
    HorizontalRoutedRouteHeaderOccurrenceBlock.output
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro token tokenMember
  cases token <;> rfl

/-- Parent descriptors expand to clause-local finite frames in linear time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

end HorizontalRoutedRouteHeaderClauseFrame
end LeanTrominoes.PeriodicCNFStripReduction

end
