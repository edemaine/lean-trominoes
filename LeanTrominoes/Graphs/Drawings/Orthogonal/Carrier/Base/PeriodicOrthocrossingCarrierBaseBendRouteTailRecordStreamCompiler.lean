/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedBinaryWordPairProductTime
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteTailRecordCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankOrderedRouteTailRecordStreamCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine
import LeanTrominoes.Computation.TM2.TM2ListAppendClosure
import LeanTrominoes.Computation.TM2.TM2PolyTimeInputEncodingTransport

/-! # Combined retained carrier-and-bend Figure 9 record streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBaseBendRouteTailRecords

open Computability Turing

def baseBendStream (descriptors : List RouteDescriptor) :
    List PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token :=
  RouteDescriptorPairAffine.affineBaseBendRouteTailRecordStream
    (RouteDescriptorPairFieldTags.inputTokens
      (DelimitedBinaryWordPairProductMachine.pairs
        (RouteDescriptorBinaryWords.words descriptors)))

def stream (descriptors : List RouteDescriptor) :
    List PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token :=
  CarrierRankOrderedPairs.retainedRouteTailRecordStream descriptors ++
    baseBendStream descriptors

noncomputable def baseBendStreamComputableInPolyTime :
    TM2ComputableInPolyTime CarrierRankOrderedPairs.InputEncoding id
      baseBendStream := by
  change TM2ComputableInPolyTime CarrierRankOrderedPairs.InputEncoding id
    (fun descriptors =>
      RouteDescriptorPairAffine.affineBaseBendRouteTailRecordStream
        (RouteDescriptorPairFieldTags.inputTokens
          (DelimitedBinaryWordPairProductMachine.pairs
            (RouteDescriptorBinaryWords.words descriptors))))
  let pairs := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
    (fun _ => rfl) (fun _ => rfl)
  let tagged := TM2CompositionMachine.computableInPolyTime pairs
    RouteDescriptorPairFieldTags.inputTokensComputableInPolyTime
  exact TM2CompositionMachine.computableInPolyTime tagged
    RouteDescriptorPairAffine.affineBaseBendRouteTailRecordStreamComputableInPolyTime

noncomputable def streamComputableInPolyTime :
    TM2ComputableInPolyTime CarrierRankOrderedPairs.InputEncoding id stream :=
  TM2ListAppend.computableInPolyTime
    CarrierRankOrderedPairs.retainedRouteTailRecordStreamComputableInPolyTime
    baseBendStreamComputableInPolyTime

end CarrierBaseBendRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing

end
