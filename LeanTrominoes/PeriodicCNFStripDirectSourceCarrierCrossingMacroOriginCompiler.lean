/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedNodeWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingMacroOriginCompiler

/-! # Direct-source compilation of crossing macrocell coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossingMacroOriginStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- Four signed coordinate columns for the actual crossing macrocell origins,
in the same global carrier order as the compiled source-key words. -/
def directSourceCarrierCrossingMacroOriginCoordinates
    (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) : List Nat :=
  CarrierCrossingMacroOrigin.values field
    (numericRouteDescriptors (directSourceFormula decider symbols))

noncomputable def
    directSourceCarrierCrossingMacroOriginCoordinatesComputableInPolyTime
    (field : CarrierCrossingMacroOrigin.Field) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceCarrierCrossingMacroOriginCoordinates decider field) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols => CarrierCrossingMacroOrigin.values field
      (numericRouteDescriptors (directSourceFormula decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    (CarrierCrossingMacroOrigin.valuesComputableInPolyTime field)

/-- The compiled columns denote physical macrocell origins, including both
signed magnitudes when carrier enumeration uses translated representatives. -/
theorem directSourceCarrierCrossingMacroOriginCoordinates_eq_nodes
    (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) :
    directSourceCarrierCrossingMacroOriginCoordinates decider field symbols =
      (CarrierCrossingMacroOrigin.nodes
        (numericRouteDescriptors (directSourceFormula decider symbols))).map
          (CarrierCrossingMacroOrigin.nodeValue field) := by
  let formula := directSourceFormula decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  unfold directSourceCarrierCrossingMacroOriginCoordinates
  exact CarrierCrossingMacroOrigin.values_numericRouteDescriptors field formula
    (PeriodicCNF.incidenceGraph_isWellFormed formula)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    isLocal
    (directSourceFormula_isForwardLocal decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)

/-- All four coordinate columns have one entry per physical carrier node. -/
theorem directSourceCarrierCrossingMacroOriginCoordinates_length
    (field : CarrierCrossingMacroOrigin.Field)
    (symbols : List encoding.Γ) :
    (directSourceCarrierCrossingMacroOriginCoordinates decider field symbols).length =
      (CarrierCrossingMacroOrigin.nodes
        (numericRouteDescriptors (directSourceFormula decider symbols))).length := by
  rw [directSourceCarrierCrossingMacroOriginCoordinates_eq_nodes]
  exact List.length_map _

/-- The existing normalized source-key compiler and the coordinate columns
refer to precisely the same physical node enumeration. -/
theorem directSourceCarrierNormalizedRankedWordTokens_eq_macroOriginNodes
    (symbols : List encoding.Γ) :
    directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens decider symbols =
      let descriptors := numericRouteDescriptors (directSourceFormula decider symbols)
      DelimitedBinaryWords.encode
        (CarrierSourcePairFieldFormatter.words
          ((CarrierCrossingMacroOrigin.nodes descriptors).map
            (CarrierNodeNormalizedSourceKeys.pairAtPeriod
              (routeDescriptorStreamGridSize descriptors)))) := by
  exact directSourceCarrierNormalizedRankedWordTokens_eq_nodes decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
