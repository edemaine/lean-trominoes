/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedBooleanListClosure
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankComparisonComponents
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankCompiler

/-! # Stable-rank compilation from component comparison streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- Atom-equality and terminal strict-order producers compose to the exact
strict-lower stable-rank square. -/
noncomputable def
    retainedOccurrenceGlobalStableLowerBitsComputableInPolyTimeOf
    {Source InputSymbol Variable : Type}
    [DecidableEq Variable] [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Source → List InputSymbol)
    (source : Source → PeriodicCNF Variable)
    (routes : Source → PositionedPeriodicCNF.IncidenceRoutes)
    (atomEqualityCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input => retainedOccurrenceGlobalAtomEqualityBits (source input)))
    (terminalStrictLowerCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalTerminalStrictLowerBits
          (source input) (routes input))) :
    @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalStableLowerBits
          (source input) (routes input)) := by
  let combined := AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeInput .conjunction
    (fun input => retainedOccurrenceGlobalAtomEqualityBits (source input))
    (fun input => retainedOccurrenceGlobalTerminalStrictLowerBits
      (source input) (routes input))
    (fun input => by simp)
    atomEqualityCompiler terminalStrictLowerCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id)
    (function₂ := fun input =>
      retainedOccurrenceGlobalStableLowerBits
        (source input) (routes input)) combined (fun input => by
      exact (retainedOccurrenceGlobalStableLowerBits_eq_components
        (source input) (routes input)).symm)

/-- Atom-equality and terminal-coordinate-equality producers compose to the
exact stable-rank tie square. -/
noncomputable def
    retainedOccurrenceGlobalStableTieBitsComputableInPolyTimeOf
    {Source InputSymbol Variable : Type}
    [DecidableEq Variable] [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Source → List InputSymbol)
    (source : Source → PeriodicCNF Variable)
    (routes : Source → PositionedPeriodicCNF.IncidenceRoutes)
    (atomEqualityCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input => retainedOccurrenceGlobalAtomEqualityBits (source input)))
    (terminalEqualityCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalTerminalEqualityBits
          (source input) (routes input))) :
    @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalStableTieBits
          (source input) (routes input)) := by
  let combined := AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeInput .conjunction
    (fun input => retainedOccurrenceGlobalAtomEqualityBits (source input))
    (fun input => retainedOccurrenceGlobalTerminalEqualityBits
      (source input) (routes input))
    (fun input => by simp)
    atomEqualityCompiler terminalEqualityCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id)
    (function₂ := fun input =>
      retainedOccurrenceGlobalStableTieBits
        (source input) (routes input)) combined (fun input => by
      exact (retainedOccurrenceGlobalStableTieBits_eq_components
        (source input) (routes input)).symm)

/-- Exact producers for atom equality, terminal strict order, and terminal
equality suffice to compile the semantic global stable-rank stream. -/
noncomputable def
    retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOfComponents
    {Source InputSymbol Variable : Type}
    [DecidableEq Variable] [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Source → List InputSymbol)
    (source : Source → PeriodicCNF Variable)
    (routes : Source → PositionedPeriodicCNF.IncidenceRoutes)
    (atomEqualityCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input => retainedOccurrenceGlobalAtomEqualityBits (source input)))
    (terminalStrictLowerCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalTerminalStrictLowerBits
          (source input) (routes input)))
    (terminalEqualityCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalTerminalEqualityBits
          (source input) (routes input))) :
    @TM2ComputableInPolyTime
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input =>
        retainedOccurrenceGlobalStableTerminalRanks
          (source input) (routes input)) :=
  retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOf
    encodeInput source routes
    (retainedOccurrenceGlobalStableLowerBitsComputableInPolyTimeOf
      encodeInput source routes atomEqualityCompiler
      terminalStrictLowerCompiler)
    (retainedOccurrenceGlobalStableTieBitsComputableInPolyTimeOf
      encodeInput source routes atomEqualityCompiler
      terminalEqualityCompiler)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
