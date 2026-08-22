/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorWordPairCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorWordPairCrossingSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler boundary for descriptor-pair crossing evaluation -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

/-- The one remaining fixed evaluator boundary: consume delimiter-encoded
descriptor-word pairs and emit their exact variable-marker stream. -/
abbrev RouteDescriptorWordPairCrossingMarkerCompiler :=
  @TM2ComputableInPolyTime
    DelimitedBinaryWordPairs.Input
    (List FormulaShapeDirectionOrdering.Token)
    DelimitedBinaryWordPairs.Token
    FormulaShapeDirectionOrdering.Token
    DelimitedBinaryWordPairs.finEncoding.encode id
    (RouteDescriptorBinaryWordPairs.crossingMarkers
      FormulaShapeDirectionOrdering.Token.variable)

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCrossingCompilerBoundaryStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Any implementation of the fixed pair evaluator composes with the verified
direct pair producer to compile the exact semantic crossing markers. -/
noncomputable def directSourceRouteDescriptorCrossingMarkersComputableInPolyTimeOf
    (evaluator : RouteDescriptorWordPairCrossingMarkerCompiler) :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token
      id id
      (fun symbols =>
        directSourceRouteDescriptorCrossingMarkers decider symbols) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorWordPairsComputableInPolyTime decider)
    evaluator
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    fun symbols => by
      simpa only [id_eq,
        directSourceRouteDescriptorWordPairCrossingMarkers] using
        directSourceRouteDescriptorWordPairCrossingMarkers_eq decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end
