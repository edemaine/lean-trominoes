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

/-- A missing terminal has the semantic north fallback used by clause fans. -/
def directionAt (headers : List Header) (index : Nat) : AxisDirection :=
  (headers[index]?).map HorizontalRoutedRouteHeader.outputFirstDirection
    |>.getD .north

/-- Assemble the finite clause fan carried by one consecutive final-clause
header block. -/
def clauseFanData (headers : List Header) : ClauseRibbonFanData where
  hasRight := decide (3 ≤ headers.length)
  direction
    | .top => directionAt headers 0
    | .left => directionAt headers 1
    | .right => directionAt headers 2

/-- Attach one common clause fan and the literal-position terminal group to
every header of a final clause. -/
def frameBlock (headers : List Header) : List Data :=
  headers.zipIdx.map fun indexed =>
    ⟨indexed.1, clauseFanData headers,
      terminalGroupOfLiteralIndex indexed.2⟩

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

/-- Complete clause-local frame stream generated by one directed parent
clause profile. -/
def sourceClauseFrames (profile : DirectedClauseProfile) : List Data :=
  let ordered := orderedDirectedProfile profile
  frames (figureClauseProfiles ordered)
    (FormulaShapeFigureNineRoutePrefix.clauseDescriptors ordered)

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
