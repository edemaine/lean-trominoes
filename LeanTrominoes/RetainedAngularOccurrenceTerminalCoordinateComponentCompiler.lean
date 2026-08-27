/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentSemantics
import LeanTrominoes.AlignedBooleanListClosure

/-! # Compiling retained terminal-coordinate components -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace TerminalCoordinateComponents

open Computability Turing

private noncomputable def pairwiseComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (operation : UnarySmallSumBooleans.Operation)
    (first second : Input → List Bool)
    (lengthEq : ∀ input,
      (first input).length = (second input).length)
    (firstCompiler : @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id first)
    (secondCompiler : @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id second) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => SignedUnaryStrictLower.pairwise operation
        (first input) (second input)) := by
  change @TM2ComputableInPolyTime
    Input (List Bool) InputSymbol Bool encodeInput id
    (fun input => List.zipWith operation.apply
      (first input) (second input))
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeInput operation first second lengthEq
    firstCompiler secondCompiler

/-- Exact unary compilers for angular ranks and radial lengths suffice for
the complete strict terminal-coordinate matrix. -/
noncomputable def strictLowerBitsComputableInPolyTimeOf
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (values : Input → List (Nat × Nat))
    (directionRankCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => directionRanks (values input)))
    (radialLengthCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => radialLengths (values input))) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => strictLowerBits (values input)) := by
  let directionLower :=
    UnaryFieldStrictLowerRows.bitsComputableInPolyTime
      encodeInput (fun input => directionRanks (values input))
      directionRankCompiler
  let directionEqual :=
    UnaryFieldEqualityRows.equalityBitsComputableInPolyTime
      encodeInput (fun input => directionRanks (values input))
      directionRankCompiler
  let radialLower :=
    UnaryFieldStrictLowerRows.bitsComputableInPolyTime
      encodeInput (fun input => radialLengths (values input))
      radialLengthCompiler
  let tiedLower := pairwiseComputableInPolyTime
    encodeInput .conjunction
    (fun input => UnaryFieldEqualityRows.equalityBits
      (directionRanks (values input)))
    (fun input => UnaryFieldStrictLowerRows.strictLowerBits
      (radialLengths (values input)))
    (fun input => by simp [directionRanks, radialLengths])
    directionEqual radialLower
  exact pairwiseComputableInPolyTime
    encodeInput .disjunction
    (fun input => UnaryFieldStrictLowerRows.strictLowerBits
      (directionRanks (values input)))
    (fun input => SignedUnaryStrictLower.pairwise .conjunction
      (UnaryFieldEqualityRows.equalityBits
        (directionRanks (values input)))
      (UnaryFieldStrictLowerRows.strictLowerBits
        (radialLengths (values input))))
    (fun input => by
      simp [SignedUnaryStrictLower.pairwise,
        directionRanks, radialLengths])
    directionLower tiedLower

/-- The same two unary component compilers also produce the complete
terminal-coordinate equality matrix. -/
noncomputable def equalityBitsComputableInPolyTimeOf
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (values : Input → List (Nat × Nat))
    (directionRankCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => directionRanks (values input)))
    (radialLengthCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => radialLengths (values input))) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => equalityBits (values input)) := by
  let directionEqual :=
    UnaryFieldEqualityRows.equalityBitsComputableInPolyTime
      encodeInput (fun input => directionRanks (values input))
      directionRankCompiler
  let radialEqual :=
    UnaryFieldEqualityRows.equalityBitsComputableInPolyTime
      encodeInput (fun input => radialLengths (values input))
      radialLengthCompiler
  exact pairwiseComputableInPolyTime
    encodeInput .conjunction
    (fun input => UnaryFieldEqualityRows.equalityBits
      (directionRanks (values input)))
    (fun input => UnaryFieldEqualityRows.equalityBits
      (radialLengths (values input)))
    (fun input => by simp [directionRanks, radialLengths])
    directionEqual radialEqual

/-- Therefore exact unary streams of the actual global direction ranks and
radial lengths compile the semantic strict terminal comparison stream. -/
noncomputable def
    retainedOccurrenceGlobalTerminalStrictLowerBitsComputableInPolyTimeOf
    {Input InputSymbol Variable : Type}
    [DecidableEq Variable]
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (directionRankCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => directionRanks
        (coordinates (source input) (routes input))))
    (radialLengthCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => radialLengths
        (coordinates (source input) (routes input)))) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => retainedOccurrenceGlobalTerminalStrictLowerBits
        (source input) (routes input)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (strictLowerBitsComputableInPolyTimeOf
      encodeInput
      (fun input => coordinates (source input) (routes input))
      directionRankCompiler radialLengthCompiler)
    (fun input =>
      (retainedOccurrenceGlobalTerminalStrictLowerBits_eq_components
        (source input) (routes input)).symm)

/-- Likewise those two unary streams compile the semantic terminal equality
stream. -/
noncomputable def
    retainedOccurrenceGlobalTerminalEqualityBitsComputableInPolyTimeOf
    {Input InputSymbol Variable : Type}
    [DecidableEq Variable]
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (directionRankCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => directionRanks
        (coordinates (source input) (routes input))))
    (radialLengthCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => radialLengths
        (coordinates (source input) (routes input)))) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => retainedOccurrenceGlobalTerminalEqualityBits
        (source input) (routes input)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (equalityBitsComputableInPolyTimeOf
      encodeInput
      (fun input => coordinates (source input) (routes input))
      directionRankCompiler radialLengthCompiler)
    (fun input =>
      (retainedOccurrenceGlobalTerminalEqualityBits_eq_components
        (source input) (routes input)).symm)

end TerminalCoordinateComponents
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
