/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRepresentativeFieldData
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers
import LeanTrominoes.PeriodicCNFStripDirectSourceVariableDecidableEqInstance
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyAllFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRepresentativeFieldLookupInput
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for direct-source normalized carrier representative fields -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedCarrierRepresentativeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

private abbrev descriptors (symbols : List encoding.Γ) :
    List RouteDescriptor :=
  numericRouteDescriptors (directSourceFormula decider symbols)

private abbrev period (symbols : List encoding.Γ) : Nat :=
  routeDescriptorStreamGridSize (descriptors decider symbols)

private abbrev lookupInput (symbols : List encoding.Γ) :
    LastTrueUnaryValueLookupMachine.Input :=
  CarrierNormalizedSourceKeyRepresentativeFieldLookup.inputAtPeriod
    (period decider symbols) (descriptors decider symbols)

private noncomputable def
    directSourceCarrierNormalizedSourceKeySelectedFieldsPreparedComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols =>
        CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
          (routeDescriptorStreamGridSize
            (numericRouteDescriptors (directSourceFormula decider symbols)))
          (numericRouteDescriptors (directSourceFormula decider symbols))) := by
  let descriptorCompiler :=
    directSourceNumericRouteDescriptorsComputableInPolyTime decider
  let descriptorRows :=
    CarrierSourceKeyRepresentativeFieldLookup.expandedRowsComputableInPolyTime
  let descriptorFields :=
    CarrierNormalizedSourceKeyAllFieldStream.emittedFieldsComputableInPolyTime
  let descriptorPair := TM2ForkMachine.computableInPolyTime
    descriptorRows descriptorFields
  let rawInput := TM2CompositionMachine.computableInPolyTime
    descriptorCompiler descriptorPair
  let inputCompiler : TM2ComputableInPolyTime id
      LastTrueUnaryValueLookupMachine.encode
      (lookupInput decider) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq rawInput
      (fun symbols => by
        have fieldsEq :=
          CarrierNormalizedSourceKeyAllFieldStream.emittedFields_eq
            (period decider symbols) (descriptors decider symbols)
            (fun descriptor descriptorMember =>
              numericRouteDescriptors_gridSize_eq_stream
          (directSourceFormula decider symbols)
          (directSource_incidencesWithMetadata_ne_nil decider symbols)
                descriptor descriptorMember)
        change SeparatedProductEncoding.encode
            DelimitedBinaryWords.finEncoding.encode id
            (CarrierSourceKeyRepresentativeFieldLookup.expandedRows
                (descriptors decider symbols),
              CarrierNormalizedSourceKeyAllFieldStream.emittedFields
                (descriptors decider symbols)) =
          LastTrueUnaryValueLookupMachine.encode
            (lookupInput decider symbols)
        unfold lookupInput
        exact
          CarrierNormalizedSourceKeyRepresentativeFieldLookup.encoded_physical_pair_eq_encode_inputAtPeriod
            (period decider symbols) (descriptors decider symbols)
            (CarrierNormalizedSourceKeyAllFieldStream.emittedFields
              (descriptors decider symbols)) fieldsEq)
  have selected : TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields
      (fun symbols =>
        CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
          (routeDescriptorStreamGridSize
            (numericRouteDescriptors (directSourceFormula decider symbols)))
          (numericRouteDescriptors (directSourceFormula decider symbols))) := by
    simpa only [lookupInput,
      CarrierNormalizedSourceKeyRepresentativeFieldLookup.lookups_inputAtPeriod]
      using
    TM2CompositionMachine.computableInPolyTime inputCompiler
      LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact selected

noncomputable abbrev
    directSourceCarrierNormalizedSourceKeySelectedFieldsComputableInPolyTime :=
  directSourceCarrierNormalizedSourceKeySelectedFieldsPreparedComputableInPolyTime
    decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
