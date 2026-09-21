/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeRouteWordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPresentedDirectionWords

/-! # Native compilation of the actual horizontal incidence direction words -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicOrthocrossing
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeRouteStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeRouteVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

/-- Actual clause-major, literal-minor words, without reversal or rescaling. -/
def nativeRouteWords (symbols : List encoding.Γ) : List (List AxisDirection) :=
  presentedIncidenceDirectionWords
    (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
    (horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))

theorem nativeRouteWords_compiled (symbols : List encoding.Γ) :
    NativeRouteWord.output (directSourceFinalCompiledRoutedRequestBlockTokens decider symbols) =
      DelimitedDirectionDisplacement.words (nativeRouteWords decider symbols) := by
  rw [directSourceFinalCompiledRoutedRequestBlockTokens_eq,
    directFigureNinePolarityRoutedRequestBlockTokens,
    directFigureNinePolarityRouteTailRecords_eq_records,
    HorizontalRoutedRouteHeaderTailBlock.output_records,
    NativeRouteWord.output_requests,
    directFigureNinePolarityRoutePairs_map_directions_eq_horizontal]
  rfl

/-- One delimiter per actual incidence, including an empty direction word. -/
noncomputable def nativeRouteWordsCompiler :
    TM2ComputableInPolyTime id id
      (fun symbols => DelimitedDirectionDisplacement.words (nativeRouteWords decider symbols)) := by
  let physical : TM2ComputableInPolyTime id id
      (fun symbols => NativeRouteWord.output
        (directSourceFinalCompiledRoutedRequestBlockTokens decider symbols)) :=
    TM2CompositionMachine.computableInPolyTime
      (directSourceFinalCompiledRoutedRequestBlockTokensComputableInPolyTime decider)
      NativeRouteWord.compiler
  simpa only [nativeRouteWords_compiled] using physical

/-- Positive or negative horizontal or vertical displacements of the actual routes. -/
noncomputable def nativeRouteDisplacementCompiler (horizontal positive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => DelimitedDirectionDisplacement.values horizontal positive
        (nativeRouteWords decider symbols)) :=
  DelimitedDirectionDisplacement.valuesComputableInPolyTime
    (nativeRouteWords decider) horizontal positive (nativeRouteWordsCompiler decider)

end LeanTrominoes.PeriodicCNFStripReduction
end
