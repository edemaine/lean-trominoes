/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCrossingMacroOriginCompiler
import LeanTrominoes.PeriodicOrthocrossingInternalCrossingCoordinateKeyCompiler

/-! # Direct role-indexed crossing keys and aligned origin columns -/

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

noncomputable local instance directInternalCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

def directSourceInternalCrossingCoordinateKeys (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  InternalCrossingCoordinateKeys.words (numericRouteDescriptors (directSourceFormula decider symbols))

private theorem baseTokens_eq_encode (symbols : List encoding.Γ) :
    InternalCrossingCoordinateKeys.baseTokens (numericRouteDescriptors (directSourceFormula decider symbols)) =
      DelimitedBinaryWords.encode (InternalCrossingCoordinateKeys.baseWords
        (numericRouteDescriptors (directSourceFormula decider symbols))) := by
  let formula := directSourceFormula decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  exact InternalCrossingCoordinateKeys.baseTokens_numericRouteDescriptors formula
    (PeriodicCNF.incidenceGraph_isWellFormed formula)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    isLocal (directSourceFormula_isForwardLocal decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)

noncomputable def directSourceInternalCrossingCoordinateKeysComputableInPolyTime :
    TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode
      (directSourceInternalCrossingCoordinateKeys decider) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    InternalCrossingCoordinateKeys.baseTokensComputableInPolyTime
  let base := wordsOutputCompiler id
    (fun symbols => InternalCrossingCoordinateKeys.baseTokens
      (numericRouteDescriptors (directSourceFormula decider symbols)))
    (fun symbols => InternalCrossingCoordinateKeys.baseWords
      (numericRouteDescriptors (directSourceFormula decider symbols)))
    physical (baseTokens_eq_encode decider)
  exact InternalCrossingCoordinateKeys.wordsComputableInPolyTime
    (fun symbols => numericRouteDescriptors (directSourceFormula decider symbols)) base

theorem directSourceInternalCrossingCoordinateKeys_eq_candidates (symbols : List encoding.Γ) :
    (directSourceInternalCrossingCoordinateKeys decider symbols).words =
      (InternalCrossingCoordinateKeys.candidates
        (numericRouteDescriptors (directSourceFormula decider symbols))).map
        InternalCrossingCoordinateKeys.nodeWord := by
  unfold directSourceInternalCrossingCoordinateKeys
  exact InternalCrossingCoordinateKeys.words_eq_candidates _

/-- Each fixed role receives a copy of the same physical crossing-origin column. -/
def directSourceInternalCrossingOriginCoordinates (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  InternalCrossingCoordinateKeys.roles.flatMap fun _ =>
    directSourceCarrierCrossingMacroOriginCoordinates decider field symbols

noncomputable def directSourceInternalCrossingOriginCoordinatesComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceInternalCrossingOriginCoordinates decider field) := by
  exact UnaryFieldEncoderMachine.flatMapComputableInPolyTime InternalCrossingCoordinateKeys.roles
    (fun _ => directSourceCarrierCrossingMacroOriginCoordinates decider field)
    (fun _ => directSourceCarrierCrossingMacroOriginCoordinatesComputableInPolyTime decider field)

theorem directSourceInternalCrossingOriginCoordinates_eq_candidates
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    directSourceInternalCrossingOriginCoordinates decider field symbols =
      (InternalCrossingCoordinateKeys.candidates
        (numericRouteDescriptors (directSourceFormula decider symbols))).map
        (fun candidate => CarrierCrossingMacroOrigin.nodeValue field candidate.2) := by
  unfold directSourceInternalCrossingOriginCoordinates
  rw [directSourceCarrierCrossingMacroOriginCoordinates_eq_nodes]
  simp only [InternalCrossingCoordinateKeys.candidates, List.map_flatMap, List.map_map,
    Function.comp_def]

theorem directSourceInternalCrossingCoordinateKeys_length_origins
    (field : CarrierCrossingMacroOrigin.Field) (symbols : List encoding.Γ) :
    (directSourceInternalCrossingCoordinateKeys decider symbols).words.length =
      (directSourceInternalCrossingOriginCoordinates decider field symbols).length := by
  rw [directSourceInternalCrossingCoordinateKeys_eq_candidates,
    directSourceInternalCrossingOriginCoordinates_eq_candidates, List.length_map, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
