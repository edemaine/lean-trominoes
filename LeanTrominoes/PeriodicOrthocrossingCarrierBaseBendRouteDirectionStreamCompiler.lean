/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteDirectionCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteDirectionStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Complete retained carrier-and-base-bend direction streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBaseBendRouteDirections

open Computability Turing

/-- Complete untranslated bend blocks obtained from the ordered square of a
canonical numeric route-descriptor stream. -/
def baseBendStream (descriptors : List RouteDescriptor) :
    List CarrierSpanRouteDirections.Token :=
  RouteDescriptorPairAffine.affineBaseBendRouteDirectionStream
    (RouteDescriptorPairFieldTags.inputTokens
      (DelimitedBinaryWordPairProductMachine.pairs
        (RouteDescriptorBinaryWords.words descriptors)))

/-- Retained carrier blocks followed by untranslated retained bend blocks. -/
def stream (descriptors : List RouteDescriptor) :
    List CarrierSpanRouteDirections.Token :=
  CarrierRankOrderedPairs.retainedRouteDirectionStream descriptors ++
    baseBendStream descriptors

/-- The untranslated retained-bend stream is polynomial-time computable from
the canonical numeric descriptor encoding. -/
noncomputable def baseBendStreamComputableInPolyTime :
    TM2ComputableInPolyTime CarrierRankOrderedPairs.InputEncoding id
      baseBendStream := by
  change TM2ComputableInPolyTime CarrierRankOrderedPairs.InputEncoding id
    (fun descriptors =>
      RouteDescriptorPairAffine.affineBaseBendRouteDirectionStream
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
    RouteDescriptorPairAffine.affineBaseBendRouteDirectionStreamComputableInPolyTime

/-- The combined retained carrier-and-bend direction stream is polynomial-time
computable from the canonical numeric descriptor encoding. -/
noncomputable def streamComputableInPolyTime :
    TM2ComputableInPolyTime CarrierRankOrderedPairs.InputEncoding id stream :=
  TM2ListAppend.computableInPolyTime
    CarrierRankOrderedPairs.retainedRouteDirectionStreamComputableInPolyTime
    baseBendStreamComputableInPolyTime

end CarrierBaseBendRouteDirections
end LeanTrominoes.PeriodicOrthocrossing

end
