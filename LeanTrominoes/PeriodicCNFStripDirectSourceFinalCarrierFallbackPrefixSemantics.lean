/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackPrefixCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackPrefixScalingStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackTerminalDataBlockStreamSemantics

/-! # Semantic scaled fallback prefixes of direct-source carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackPrefixSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackPrefixSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Deduplicated globally ranked carrier entries reconstructed from the
direct source. -/
def directSourceFinalCarrierFallbackEntries
    (symbols : List encoding.Γ) :
    List CarrierFallbackTerminalData.IndexedCarrierEntry :=
  let descriptors :=
    numericRouteDescriptors (directSourceFormula decider symbols)
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  entries.zipIdx

/-- Axis and positive span of each retained carrier, in the compiler's
row-major global-rank order. -/
def directSourceFinalCarrierFallbackPrefixBlocks
    (symbols : List encoding.Γ) : List (Bool × Nat) :=
  CarrierFallbackTerminalData.selectedBlocks
    (directSourceFinalCarrierFallbackEntries decider symbols)

/-- Four fixed-clearance undelimited prefix words per retained carrier. -/
def directSourceFinalCarrierFallbackPrefixWords
    (symbols : List encoding.Γ) : List (List AxisDirection) :=
  (directSourceFinalCarrierFallbackPrefixBlocks
    decider symbols).flatMap fun block =>
      CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
        block.1 block.2

private theorem directSourceCarrierRouteDirectionBlocks_eq_prefixBlocks
    (symbols : List encoding.Γ) :
    directSourceCarrierRouteDirectionBlocks decider symbols =
      (directSourceFinalCarrierFallbackPrefixBlocks
        decider symbols).flatMap fun block =>
          CarrierSpanRouteDirections.canonicalBlock block.1 block.2 := by
  rw [directSourceCarrierRouteDirectionBlocks_eq]
  unfold directSourceFinalCarrierFallbackPrefixBlocks
    directSourceFinalCarrierFallbackEntries
    CarrierFallbackTerminalData.selectedBlocks
  simp only [List.flatMap_assoc]
  apply List.flatMap_congr
  intro first _firstMember
  apply List.flatMap_congr
  intro second _secondMember
  by_cases retained :
      CarrierRankOrderedPairs.retainedPredicate first second
  · simp [retained]
  · simp [retained]

theorem directSourceFinalCarrierFallbackPrefixBlocks_spanLarge
    (symbols : List encoding.Γ) :
    ∀ block ∈ directSourceFinalCarrierFallbackPrefixBlocks
        decider symbols,
      6 < block.2 := by
  let formula := directSourceFormula decider symbols
  let descriptors := numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have large :=
    CarrierRankOrderedPairs.retainedPredicate_spanLarge_numericRouteDescriptors
      formula
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold formula directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSource_incidencesWithMetadata_ne_nil decider symbols)
  unfold directSourceFinalCarrierFallbackPrefixBlocks
    directSourceFinalCarrierFallbackEntries
    CarrierFallbackTerminalData.selectedBlocks
  change ∀ block ∈
      (entries.zipIdx.flatMap fun first =>
        entries.zipIdx.flatMap fun second =>
          if CarrierRankOrderedPairs.retainedPredicate first second then
            [(first.1.1.horizontal,
              (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat)]
          else []),
    6 < block.2
  change ∀ first ∈ entries.zipIdx, ∀ second ∈ entries.zipIdx,
      CarrierRankOrderedPairs.retainedPredicate first second = true →
        6 < (second.1.1.orderCoordinate -
          first.1.1.orderCoordinate).toNat at large
  intro block blockMember
  rcases List.mem_flatMap.mp blockMember with
    ⟨first, firstMember, blockMember⟩
  rcases List.mem_flatMap.mp blockMember with
    ⟨second, secondMember, blockMember⟩
  by_cases retained :
      CarrierRankOrderedPairs.retainedPredicate first second
  · have blockEq :
        block =
          (first.1.1.horizontal,
            (second.1.1.orderCoordinate -
              first.1.1.orderCoordinate).toNat) := by
      simpa [retained] using blockMember
    rw [blockEq]
    exact large first firstMember second secondMember retained
  · simp [retained] at blockMember

@[simp] theorem directSourceFinalCarrierFallbackPrefixWords_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierFallbackPrefixWords
      decider symbols).length =
      4 * (directSourceFinalCarrierFallbackPrefixBlocks
        decider symbols).length := by
  simp [directSourceFinalCarrierFallbackPrefixWords,
    List.length_flatMap]
  omega

/-- The direct carrier prefix compiler emits exactly the four explicit,
fixed-clearance source-prefix words of every retained carrier. -/
theorem directSourceFinalCarrierFallbackPrefixDirections_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackPrefixDirections decider symbols =
      (directSourceFinalCarrierFallbackPrefixWords
        decider symbols).flatMap DelimitedRouteJoin.delimited := by
  unfold directSourceFinalCarrierFallbackPrefixDirections
  rw [directSourceCarrierRouteDirectionBlocks_eq_prefixBlocks]
  rw [CarrierFallbackPrefixScaling.output_flatMap_canonicalBlocks
    (directSourceFinalCarrierFallbackPrefixBlocks decider symbols)
    (directSourceFinalCarrierFallbackPrefixBlocks_spanLarge
      decider symbols)]
  unfold directSourceFinalCarrierFallbackPrefixWords
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro block _blockMember
  exact
    CarrierFallbackPrefixScaling.canonicalScaledPrefixBlock_eq_flatMap_delimited
      block.1 block.2

end LeanTrominoes.PeriodicCNFStripReduction

end
