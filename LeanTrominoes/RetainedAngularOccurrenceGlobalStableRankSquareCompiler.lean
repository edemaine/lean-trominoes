/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankPipelineData
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler preparation of global occurrence stable-rank squares -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- Any polynomial-time producer of the flat strict-lower bits also produces
their promised Boolean square input in polynomial time. -/
noncomputable def
    retainedOccurrenceGlobalStableLowerSquareInputComputableInPolyTimeOf
    {Source InputSymbol Variable : Type}
    [DecidableEq Variable]
    (encodeInput : Source → List InputSymbol)
    (source : Source → PeriodicCNF Variable)
    (routes : Source → PositionedPeriodicCNF.IncidenceRoutes)
    (bitsCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalStableLowerBits
          (source input) (routes input))) :
    @TM2ComputableInPolyTime
      Source BoolSquareRows.Input InputSymbol Bool
      encodeInput BoolSquareRows.finEncoding.encode
      (fun input =>
        retainedOccurrenceGlobalStableLowerSquareInput
          (source input) (routes input)) :=
  @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    Source (List Bool) BoolSquareRows.Input InputSymbol Bool
    encodeInput id BoolSquareRows.finEncoding.encode
    (fun input =>
      retainedOccurrenceGlobalStableLowerBits
        (source input) (routes input))
    (fun input =>
      retainedOccurrenceGlobalStableLowerSquareInput
        (source input) (routes input))
    bitsCompiler (fun input => by
      rw [BoolSquareRows.finEncoding_encode_eq_bits]
      rfl)

/-- Any polynomial-time producer of the flat equal-coordinate bits also
produces their promised Boolean square input in polynomial time. -/
noncomputable def
    retainedOccurrenceGlobalStableTieSquareInputComputableInPolyTimeOf
    {Source InputSymbol Variable : Type}
    [DecidableEq Variable]
    (encodeInput : Source → List InputSymbol)
    (source : Source → PeriodicCNF Variable)
    (routes : Source → PositionedPeriodicCNF.IncidenceRoutes)
    (bitsCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalStableTieBits
          (source input) (routes input))) :
    @TM2ComputableInPolyTime
      Source BoolSquareRows.Input InputSymbol Bool
      encodeInput BoolSquareRows.finEncoding.encode
      (fun input =>
        retainedOccurrenceGlobalStableTieSquareInput
          (source input) (routes input)) :=
  @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    Source (List Bool) BoolSquareRows.Input InputSymbol Bool
    encodeInput id BoolSquareRows.finEncoding.encode
    (fun input =>
      retainedOccurrenceGlobalStableTieBits
        (source input) (routes input))
    (fun input =>
      retainedOccurrenceGlobalStableTieSquareInput
        (source input) (routes input))
    bitsCompiler (fun input => by
      rw [BoolSquareRows.finEncoding_encode_eq_bits]
      rfl)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
