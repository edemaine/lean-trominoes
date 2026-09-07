/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseDirectionSemantics

/-! # Recovering clause frames from their ordered headers -/

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderClauseFrame

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

private theorem finalFrameBlocks_eq_frameBlock
    (profiles : List ClauseProfile)
    (prefixes : List HorizontalRoutedRouteHeader.PrefixDescriptor) :
    ∀ block ∈ finalFrameBlocks profiles prefixes,
      ∃ headers, block = frameBlock headers := by
  induction profiles generalizing prefixes with
  | nil => simp [finalFrameBlocks]
  | cons profile profiles induction =>
      intro block member
      simp only [finalFrameBlocks, List.mem_append] at member
      rcases member with member | member
      · obtain ⟨headers, _, equal⟩ := List.mem_map.mp member
        exact ⟨headers, equal.symm⟩
      · exact induction _ block member

/-- The global boundary-preserving stream consists of genuine `frameBlock`
outputs, with the same clause fan and the exact literal-index groups. -/
theorem outputBlock_eq_frameBlock
    (source : List Token) (block : List Data)
    (member : block ∈ outputBlocks source) :
    ∃ headers, block = frameBlock headers := by
  rcases List.mem_flatMap.mp member with ⟨token, _, blockMember⟩
  cases token with
  | «variable» => simp [tokenBlocks] at blockMember
  | clause profile =>
      exact finalFrameBlocks_eq_frameBlock _ _ block blockMember

/-- Retained headers completely determine every actual clause frame block. -/
theorem outputBlock_eq_frameBlock_map_header
    (source : List Token) (block : List Data)
    (member : block ∈ outputBlocks source) :
    block = frameBlock (block.map Data.header) := by
  obtain ⟨headers, rfl⟩ := outputBlock_eq_frameBlock source block member
  rw [frameBlock_map_header]

/-- The terminal groups follow the actual literal indices inside each
clause block. -/
theorem outputBlock_groups
    (source : List Token) (block : List Data)
    (member : block ∈ outputBlocks source) :
    block.map Data.group =
      (List.range block.length).map terminalGroupOfLiteralIndex := by
  obtain ⟨headers, rfl⟩ := outputBlock_eq_frameBlock source block member
  simp only [frameBlock, List.map_map, List.length_map, List.length_zipIdx]
  change headers.zipIdx.map (terminalGroupOfLiteralIndex ∘ Prod.snd) = _
  rw [← List.map_map, List.zipIdx_map_snd]
  rw [← List.range_eq_range']

/-- Every literal frame carries its clause's common fan and its own terminal group. -/
theorem outputBlock_fan_groups
    (source : List Token) (block : List Data)
    (member : block ∈ outputBlocks source) :
    block.map (fun frame => (frame.clauseFan, frame.group)) =
      (List.range block.length).map fun index =>
        (blockFan block, terminalGroupOfLiteralIndex index) := by
  obtain ⟨headers, rfl⟩ := outputBlock_eq_frameBlock source block member
  cases headers with
  | nil => rfl
  | cons header headers =>
      have fanEq : blockFan (frameBlock (header :: headers)) =
          clauseFanData (header :: headers) := by
        simp [blockFan, frameBlock, frameAt]
      rw [fanEq]
      simp only [frameBlock, List.map_map, List.length_map, List.length_zipIdx,
        frameAt, Function.comp_def]
      change (header :: headers).zipIdx.map
          ((fun index => (clauseFanData (header :: headers), terminalGroupOfLiteralIndex index)) ∘
            Prod.snd) = _
      rw [← List.map_map, List.zipIdx_map_snd, ← List.range_eq_range']

/-- A clause fan assembled directly from its incoming direction list. -/
def fanOfDirections (directions : List AxisDirection) : ClauseRibbonFanData where
  hasRight := decide (3 ≤ directions.length)
  direction
    | .top => (directions[0]?).getD .north
    | .left => (directions[1]?).getD .north
    | .right => (directions[2]?).getD .north

theorem clauseFanData_eq_fanOfDirections (headers : List Header) :
    clauseFanData headers = fanOfDirections
      (headers.map fun header => (HorizontalRoutedRouteHeader.outputFirstDirection header).opposite) := by
  unfold clauseFanData fanOfDirections
  apply congrArg₂ ClauseRibbonFanData.mk
  · simp
  · funext group
    cases group <;> simp [directionAt]

/-- The common fan of a nonempty actual clause block is determined by the
incoming directions of its retained headers. -/
theorem outputBlock_fan
    (source : List Token) (block : List Data)
    (member : block ∈ outputBlocks source) (nonempty : block ≠ []) :
    blockFan block = fanOfDirections
      (block.map fun frame => (HorizontalRoutedRouteHeader.outputFirstDirection frame.header).opposite) := by
  obtain ⟨headers, rfl⟩ := outputBlock_eq_frameBlock source block member
  cases headers with
  | nil => simp [frameBlock] at nonempty
  | cons header headers =>
      rw [show
        (frameBlock (header :: headers)).map
            (fun frame => (HorizontalRoutedRouteHeader.outputFirstDirection frame.header).opposite) =
          (header :: headers).map
            (fun header => (HorizontalRoutedRouteHeader.outputFirstDirection header).opposite) by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map fun header : Header =>
            (HorizontalRoutedRouteHeader.outputFirstDirection header).opposite)
            (frameBlock_map_header (header :: headers))]
      rw [← clauseFanData_eq_fanOfDirections]
      simp [blockFan, frameBlock, frameAt]

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderClauseFrame
