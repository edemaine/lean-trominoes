/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTime
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountTime
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankSquareCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for global occurrence stable-rank row counts -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- Any polynomial-time strict-lower bit producer composes through square
reshaping and full-row true counting. -/
opaque retainedOccurrenceGlobalStableLowerCountsComputableInPolyTimeOf
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
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input =>
        retainedOccurrenceGlobalStableLowerCounts
          (source input) (routes input)) := by
  let rowCompiler := TM2CompositionMachine.computableInPolyTime
    (retainedOccurrenceGlobalStableLowerSquareInputComputableInPolyTimeOf
      encodeInput source routes bitsCompiler)
    BoolSquareRowsMachine.computableInPolyTime
  let counted := TM2CompositionMachine.computableInPolyTime rowCompiler
    DelimitedBinaryWordTrueCounts.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := fun input =>
      retainedOccurrenceGlobalStableLowerCounts
        (source input) (routes input)) counted (fun input => by
      rfl)

/-- Any polynomial-time equal-coordinate bit producer composes through
square reshaping and successively longer prefix counting. -/
opaque retainedOccurrenceGlobalStableTieCountsComputableInPolyTimeOf
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
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input =>
        retainedOccurrenceGlobalStableTieCounts
          (source input) (routes input)) := by
  let rowCompiler := TM2CompositionMachine.computableInPolyTime
    (retainedOccurrenceGlobalStableTieSquareInputComputableInPolyTimeOf
      encodeInput source routes bitsCompiler)
    BoolSquareRowsMachine.computableInPolyTime
  let counted := TM2CompositionMachine.computableInPolyTime rowCompiler
    DelimitedBinaryWordPrefixTrueCountMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := fun input =>
      retainedOccurrenceGlobalStableTieCounts
        (source input) (routes input)) counted (fun input => by
      rfl)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
