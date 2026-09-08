/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCrossingMacroOriginCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingCoordinateKeyCompiler

/-! # Direct source-pair keys aligned with crossing-origin coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

private opaque wordsOutputCompiler
    {Source InputSymbol : Type} [Fintype InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (physicalWords : Source → List DelimitedBinaryWords.Token)
    (semanticWords : Source → DelimitedBinaryWords.Input)
    (physical : TM2ComputableInPolyTime encodeSource id physicalWords)
    (correct : ∀ source, physicalWords source = DelimitedBinaryWords.encode (semanticWords source)) :
    TM2ComputableInPolyTime encodeSource DelimitedBinaryWords.finEncoding.encode semanticWords := by
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical correct

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossingCoordinateKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- Boundary-tagged physical source-pair keys in the crossing-origin column order. -/
def directSourceCrossingCoordinateKeys (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  CarrierCrossingCoordinateKeys.words (numericRouteDescriptors (directSourceFormula decider symbols))

private theorem tokens_eq_encode (symbols : List encoding.Γ) :
    CarrierCrossingCoordinateKeys.tokens (numericRouteDescriptors (directSourceFormula decider symbols)) =
      DelimitedBinaryWords.encode (directSourceCrossingCoordinateKeys decider symbols) := by
  let formula := directSourceFormula decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  exact CarrierCrossingCoordinateKeys.tokens_numericRouteDescriptors formula
    (PeriodicCNF.incidenceGraph_isWellFormed formula)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    isLocal (directSourceFormula_isForwardLocal decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)

/-- All descriptor-validity requirements are discharged for the direct source. -/
noncomputable def directSourceCrossingCoordinateKeysComputableInPolyTime :
    TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode
      (directSourceCrossingCoordinateKeys decider) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    CarrierCrossingCoordinateKeys.tokensComputableInPolyTime
  exact wordsOutputCompiler id
    (fun symbols => CarrierCrossingCoordinateKeys.tokens
      (numericRouteDescriptors (directSourceFormula decider symbols)))
    (directSourceCrossingCoordinateKeys decider) physical (tokens_eq_encode decider)

theorem directSourceCrossingCoordinateKeys_eq_nodes (symbols : List encoding.Γ) :
    (directSourceCrossingCoordinateKeys decider symbols).words =
      (CarrierCrossingMacroOrigin.nodes (numericRouteDescriptors (directSourceFormula decider symbols))).map
        CarrierCrossingCoordinateKeys.nodeWord := by
  unfold directSourceCrossingCoordinateKeys
  exact CarrierCrossingCoordinateKeys.words_words _

/-- Every key has exactly one entry in each signed crossing-origin column. -/
theorem directSourceCrossingCoordinateKeys_length_origins
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    (directSourceCrossingCoordinateKeys decider symbols).words.length =
      (directSourceCarrierCrossingMacroOriginCoordinates decider field symbols).length := by
  rw [directSourceCrossingCoordinateKeys_eq_nodes, List.length_map,
    directSourceCarrierCrossingMacroOriginCoordinates_length]

end LeanTrominoes.PeriodicCNFStripReduction

end
