/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteTrominoPrefillTableCompiler

/-! # Finite tromino verification directly from unary coordinate input

The input supplies region cells and placed trominoes, followed by certificate
bits. The machine generates and deduplicates all candidate footprints itself.
-/
noncomputable section
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing
open EncodedUnaryColumn FiniteVerifier

private def regionCodes :
    Compiler encode (fun input => input.1.cells) (fun _ cell => Encodable.encode cell) :=
  pair regionX regionY

private def regionWords :
    TM2ComputableInPolyTime encode DelimitedBinaryWords.encode
      (fun input => ⟨input.1.cells.map cellWord⟩) := by
  let computed := TM2CompositionMachine.computableInPolyTime regionCodes
    NativeNatBinaryWords.unaryComputableInPolyTime
  exact computed.of_eq (fun _ => by simp [cellWord,List.map_map])

private def tagWords {Source InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
    {encodeSource : Source → List InputSymbol} {words : Source → DelimitedBinaryWords.Input}
    (compiler : TM2ComputableInPolyTime encodeSource DelimitedBinaryWords.encode words)
    (tag : DelimitedBinaryWords.Token → FiniteExactCoverVerifier.Token) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => (DelimitedBinaryWords.encode (words source)).map tag) := by
  let tagged := TM2PolyTimeInputEncodingTransport.of_prepare DelimitedBinaryWords.encode
    (FiniteBlockTransducer.computableInPolyTime (fun token => [tag token]))
    (fun _ => rfl) (fun _ => rfl)
  let computed := TM2CompositionMachine.computableInPolyTime compiler tagged
  exact computed.of_eq (fun _ => List.map_eq_flatMap.symm)

def bitProjection : Token → List FiniteExactCoverVerifier.Token
  | .field _ _ => []
  | .bit value => [.bit value]

private theorem flatMap_empty {α β : Type} (source : List α) :
    source.flatMap (fun _ => ([] : List β))=[] := by
  induction source <;> simp_all

private def certificateTokens : TM2ComputableInPolyTime encode id
    (fun input => input.2.map FiniteExactCoverVerifier.Token.bit) := by
  let computed := TM2PolyTimeInputEncodingTransport.of_prepare encode
    (FiniteBlockTransducer.computableInPolyTime bitProjection)
    (fun _ => rfl) (fun _ => rfl)
  exact computed.of_eq (fun input => by
    simp [encode,encodeInput,fields,List.flatMap_map,bitProjection,flatMap_empty,← List.map_eq_flatMap])

def geometricRequest (t : Tromino) (input : Input × List Bool) : FiniteExactCoverVerifier.Request :=
  nativeRequest t input.1.cells (input.1.prefill.map fun p => p.cells (fun _ => t.cells)) input.2

/-- Emit the whole exact-cover request from its original coordinate input. -/
def requestComputableInPolyTime (t : Tromino) :
    TM2ComputableInPolyTime encode FiniteExactCoverVerifier.Request.encode (geometricRequest t) := by
  let computed := TM2ListAppend.computableInPolyTime
    (tagWords regionWords FiniteExactCoverVerifier.Token.region)
    (TM2ListAppend.computableInPolyTime
      (tagWords (candidateTableComputableInPolyTime t) FiniteExactCoverVerifier.Token.candidate)
      (TM2ListAppend.computableInPolyTime
        (tagWords (prefillTableComputableInPolyTime t) FiniteExactCoverVerifier.Token.required)
        certificateTokens))
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq computed
  intro input
  simp [geometricRequest,nativeRequest,FiniteExactCoverVerifier.Request.encode,tileKey,
    List.map_map,List.append_assoc,Function.comp_def]
  rfl

/-- The complete verifier includes the candidate-table generator. -/
def nativeComputableInPolyTime (strict : Bool) (t : Tromino) :
    TM2ComputableInPolyTime encode (fun bit : Bool => [bit])
      (fun input => FiniteExactCoverVerifier.check strict (geometricRequest t input)) :=
  TM2CompositionMachine.computableInPolyTime (requestComputableInPolyTime t)
    (FiniteExactCoverVerifier.computableInPolyTime strict)

end LeanTrominoes.Tromino.FiniteCoordinateColumns
