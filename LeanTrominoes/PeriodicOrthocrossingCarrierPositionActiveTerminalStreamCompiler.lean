/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPositionActiveTerminalCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamSemantics

/-! # Exact physical terminal positions from numeric descriptor streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.ActiveTerminalCoordinateFieldStream

open Computability Turing RouteDescriptorPairAffine
open PaddedSupportedLastRepresentativeEqualityRows

/-- Only genuine terminal coordinates, with both endpoints in the established
neighboring-occurrence order. -/
def values (horizontal keepPositive : Bool)
    (descriptors : List RouteDescriptor) : List Nat :=
  (descriptors ×ˢ descriptors).flatMap fun pair =>
    activeTerminalCoordinateFields horizontal keepPositive
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

private def fields (horizontal keepPositive : Bool)
    (input : DelimitedBinaryWords.Input) : List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput RouteDescriptorPairFieldTags.isPairEnd
    (fun tokens => UnaryFieldEncoderMachine.unaryFields
      (activeTerminalCoordinateFields horizontal keepPositive tokens))
    (CarrierKeyRecipeStream.terminalTags input)

private opaque encodedOutputCompiler
    {Domain InputSymbol : Type}
    (encodeInput : Domain → List InputSymbol)
    (function : Domain → List Nat)
    (compiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields function) :
    TM2ComputableInPolyTime encodeInput id
      (fun input => UnaryFieldEncoderMachine.unaryFields (function input)) := by
  exact @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    Domain (List Nat) (List UnaryFieldEncoderMachine.Symbol)
    InputSymbol UnaryFieldEncoderMachine.Symbol encodeInput
    UnaryFieldEncoderMachine.unaryFields id function
    (fun input => UnaryFieldEncoderMachine.unaryFields (function input))
    compiler (fun _ => rfl)

private noncomputable def fieldsComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (fields horizontal keepPositive) := by
  let blockCompiler : TM2ComputableInPolyTime id id
      (fun tokens => UnaryFieldEncoderMachine.unaryFields
        (activeTerminalCoordinateFields horizontal keepPositive tokens)) :=
    encodedOutputCompiler id (activeTerminalCoordinateFields horizontal keepPositive)
      (activeTerminalCoordinateFieldsComputableInPolyTime horizontal keepPositive)
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TM2EndDelimitedBlockMap.mappedOutput
      RouteDescriptorPairFieldTags.isPairEnd
      (fun tokens => UnaryFieldEncoderMachine.unaryFields
        (activeTerminalCoordinateFields horizontal keepPositive tokens))
      (CarrierKeyRecipeStream.terminalTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.terminalTagsComputableInPolyTime
    (TM2EndDelimitedBlockMap.computableInPolyTime blockCompiler
      RouteDescriptorPairFieldTags.isPairEnd)

private theorem fields_descriptorWords (horizontal keepPositive : Bool)
    (descriptors : List RouteDescriptor) :
    fields horizontal keepPositive (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields (values horizontal keepPositive descriptors) := by
  unfold fields values
  rw [CarrierKeyRecipeStream.terminalTags_descriptorWords,
    RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

noncomputable def valuesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields (values horizontal keepPositive) := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words (fieldsComputableInPolyTime horizontal keepPositive)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (fields_descriptorWords horizontal keepPositive)

/-- Every output field names its actual terminal in the compact physical-node
stream, rather than an inactive slot of the descriptor-square enumeration. -/
theorem values_eq_activeNodes (horizontal keepPositive : Bool) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors, descriptor.gridSize = period) :
    values horizontal keepPositive descriptors =
      ((paddedTerminalCarrierNodeCandidateStream descriptors).filterMap Candidate.value).map
        (carrierNodeCoordinateFieldAtPeriod horizontal keepPositive period) := by
  unfold values paddedTerminalCarrierNodeCandidateStream
  rw [List.filterMap_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro pair pairMember
  have firstMember := (List.mem_product.mp pairMember).1
  rw [activeTerminalCoordinateFields_descriptorPairTokens, periodEq pair.1 firstMember]

/-- On actual numeric source routes, the compiler emits both coordinates of
every endpoint in the canonical neighboring-segment enumeration. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (horizontal keepPositive : Bool) (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values horizontal keepPositive (PeriodicCNF.numericRouteDescriptors formula) =
      ((routeDescriptorNeighborOccurrences (PeriodicCNF.numericRouteDescriptors formula)).flatMap
        occurrenceCarrierTerminalNodes).map
          (carrierNodeCoordinateFieldAtPeriod horizontal keepPositive
            (routeDescriptorStreamGridSize (PeriodicCNF.numericRouteDescriptors formula))) := by
  rw [values_eq_activeNodes horizontal keepPositive
    (routeDescriptorStreamGridSize (PeriodicCNF.numericRouteDescriptors formula))
    (PeriodicCNF.numericRouteDescriptors formula)
    (numericRouteDescriptors_gridSize_eq_stream formula nonempty)]
  rw [paddedTerminalCarrierNodeCandidateStream_numericRouteDescriptors
    formula wellFormed degree isLocal forward]

end LeanTrominoes.PeriodicOrthocrossing.ActiveTerminalCoordinateFieldStream

end
