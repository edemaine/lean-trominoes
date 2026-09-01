/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinSemantics
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.DelimitedRouteJoinTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for finite-alphabet delimited joining -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetDelimitedBlockJoin

open Computability Turing

variable {Alphabet : Type} [Fintype Alphabet]

/-- The finite unary route codec is a fixed block transduction. -/
noncomputable def encodedComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (encoded (Alphabet := Alphabet)) :=
  FiniteBlockTransducer.computableInPolyTime
    (encodedToken (Alphabet := Alphabet))

/-- Expanding route symbols to unary decoder symbols is a fixed block
transduction. -/
noncomputable def routeUnaryComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (routeUnary (Alphabet := Alphabet)) :=
  FiniteBlockTransducer.computableInPolyTime
    (routeUnaryBlock (Alphabet := Alphabet))

noncomputable def rawPairsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (rawPairs (Alphabet := Alphabet)) := by
  let decoder := FiniteStateTransducer.computableInPolyTime
    (FiniteIndexSlotUnaryDecoder.zero (Fintype.card (Token Alphabet)))
    (FiniteIndexSlotUnaryDecoder.transition
      (count := Fintype.card (Token Alphabet)))
    (FiniteIndexSlotUnaryDecoder.finish
      (count := Fintype.card (Token Alphabet)))
  let complete := TM2CompositionMachine.computableInPolyTime
    (routeUnaryComputableInPolyTime (Alphabet := Alphabet)) decoder
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
    (fun _ => rfl)

noncomputable def decodedComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (decoded (Alphabet := Alphabet)) := by
  let complete := TM2CompositionMachine.computableInPolyTime
    (rawPairsComputableInPolyTime (Alphabet := Alphabet))
    (FiniteBlockTransducer.computableInPolyTime fun pair : Pair Alphabet =>
      [pairToken (Alphabet := Alphabet) pair])
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
    (fun input => by
      unfold decoded
      rw [← List.map_eq_flatMap])

/-- Two end-delimited streams compiled from the same source can be joined
pointwise in polynomial time over any finite payload alphabet. -/
noncomputable def joinedComputableInPolyTimeOf
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (prefixes suffixes : Source → List (Token Alphabet))
    (prefixCompiler :
      @TM2ComputableInPolyTime
        Source (List (Token Alphabet)) SourceSymbol (Token Alphabet)
        encodeSource id prefixes)
    (suffixCompiler :
      @TM2ComputableInPolyTime
        Source (List (Token Alphabet)) SourceSymbol (Token Alphabet)
        encodeSource id suffixes) :
    @TM2ComputableInPolyTime
      Source (List (Token Alphabet)) SourceSymbol (Token Alphabet)
      encodeSource id
      (fun source => joined (prefixes source) (suffixes source)) := by
  let encodedPrefixes := TM2CompositionMachine.computableInPolyTime
    prefixCompiler (encodedComputableInPolyTime (Alphabet := Alphabet))
  let encodedSuffixes := TM2CompositionMachine.computableInPolyTime
    suffixCompiler (encodedComputableInPolyTime (Alphabet := Alphabet))
  let routedJoin := DelimitedRouteJoin.joinedComputableInPolyTimeOf
    encodeSource
    (fun source => encoded (Alphabet := Alphabet) (prefixes source))
    (fun source => encoded (Alphabet := Alphabet) (suffixes source))
    encodedPrefixes encodedSuffixes
  exact TM2CompositionMachine.computableInPolyTime routedJoin
    (decodedComputableInPolyTime (Alphabet := Alphabet))

end LeanTrominoes.FiniteAlphabetDelimitedBlockJoin

end
