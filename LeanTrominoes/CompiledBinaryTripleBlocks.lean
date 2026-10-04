/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BinaryWordTripleBlocks
import LeanTrominoes.UnarySortedTripleCompiler

/-! # Packing three compiled natural fields per row -/
noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
variable {Input Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {encodeInput : Input → List Symbol} {rows : Input → List Index}
  {f g h : Input → Index → Nat}

def packedTriples (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g)
    (c : Compiler encodeInput rows h) :
    TM2ComputableInPolyTime encodeInput DelimitedBinaryWords.encode
      (fun s => ⟨(rows s).map fun i => BinaryWordBlocks.pack
        [encodeNat (f s i),encodeNat (g s i),encodeNat (h s i)]⟩) := by
  let binary := TM2CompositionMachine.computableInPolyTime (triple a b c)
    NativeNatBinaryWords.unaryComputableInPolyTime
  let triples (s : Input) := (rows s).map fun i =>
    (encodeNat (f s i),encodeNat (g s i),encodeNat (h s i))
  let prepared : TM2ComputableInPolyTime encodeInput
      (fun triples => DelimitedBinaryWords.encode (BinaryWordTripleBlocks.input triples)) triples :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq binary (fun s => by
      simp [triples,BinaryWordTripleBlocks.input,List.map_flatMap,List.flatMap_map])
  let composed := TM2CompositionMachine.computableInPolyTime prepared BinaryWordTripleBlocks.computableInPolyTime
  exact composed.of_eq (fun _ => by simp [BinaryWordTripleBlocks.output,triples,List.map_map])

end LeanTrominoes.EncodedUnaryColumn
