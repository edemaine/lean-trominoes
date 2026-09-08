/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedDirectionDisplacementCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledRouteTailRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockSemantics

/-! # Exact signed displacements of the compiled retained source tails -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing

private def tailDirectionBlock : HorizontalRoutedRouteHeaderTail.Token →
    List DelimitedDirectionDisplacement.Token
  | .header _ => []
  | .tailDirection direction => [.direction direction]
  | .recordEnd => [.routeEnd]

private theorem tailDirectionBlock_records
    (pairs : List (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    (HorizontalRoutedRouteHeaderTail.records pairs).flatMap tailDirectionBlock =
      DelimitedDirectionDisplacement.words (pairs.map Prod.snd) := by
  simp only [HorizontalRoutedRouteHeaderTail.records, List.flatMap_assoc,
    DelimitedDirectionDisplacement.words, List.flatMap_map]
  apply List.flatMap_congr
  intro pair _member
  simp [HorizontalRoutedRouteHeaderTail.record, DelimitedDirectionDisplacement.word,
    tailDirectionBlock, List.flatMap_map, ← List.map_eq_flatMap]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance tailDisplacementStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Drop finite headers while preserving every tail word and record boundary. -/
def directSourceFinalTailDirectionTokens (symbols : List encoding.Γ) :=
  (directSourceFinalCompiledRouteTailRecords decider symbols).flatMap tailDirectionBlock

noncomputable def directSourceFinalTailDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalTailDirectionTokens decider) := by
  unfold directSourceFinalTailDirectionTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCompiledRouteTailRecordsComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime tailDirectionBlock)

theorem directSourceFinalTailDirectionTokens_eq_words (symbols : List encoding.Γ) :
    directSourceFinalTailDirectionTokens decider symbols =
      DelimitedDirectionDisplacement.words
        ((directFigureNinePolarityRoutePairs decider symbols).map Prod.snd) := by
  rw [directSourceFinalTailDirectionTokens, directSourceFinalCompiledRouteTailRecords_eq,
    directFigureNinePolarityRouteTailRecords_eq_records, tailDirectionBlock_records]

/-- Signed tail displacement in the complete final occurrence order. -/
def directSourceFinalTailDisplacements (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :=
  DelimitedDirectionDisplacement.values horizontal keepPositive
    ((directFigureNinePolarityRoutePairs decider symbols).map Prod.snd)

noncomputable def directSourceFinalTailDisplacementsComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTailDisplacements decider horizontal keepPositive) := by
  apply DelimitedDirectionDisplacement.valuesComputableInPolyTime
    (fun symbols => (directFigureNinePolarityRoutePairs decider symbols).map Prod.snd)
    horizontal keepPositive
  rw [← funext (directSourceFinalTailDirectionTokens_eq_words decider)]
  exact directSourceFinalTailDirectionTokensComputableInPolyTime decider

/-- Each compiled field is the signed magnitude of its actual retained tail. -/
theorem directSourceFinalTailDisplacements_eq_pairs
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalTailDisplacements decider horizontal keepPositive symbols =
      (directFigureNinePolarityRoutePairs decider symbols).map fun pair =>
        SignedUnaryCoordinateRefinement.field keepPositive
          (DelimitedDirectionDisplacement.displacement horizontal pair.2) := by
  rw [directSourceFinalTailDisplacements, DelimitedDirectionDisplacement.values_eq_displacements,
    List.map_map]
  rfl

@[simp] theorem directSourceFinalTailDisplacements_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalTailDisplacements decider horizontal keepPositive symbols).length =
      (directFigureNinePolarityRoutePairs decider symbols).length := by
  rw [directSourceFinalTailDisplacements_eq_pairs, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
