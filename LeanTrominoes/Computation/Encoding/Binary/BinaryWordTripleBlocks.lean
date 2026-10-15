/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Binary.BinaryWordBlocks
import LeanTrominoes.Complexity.FiniteStateTransducerSemantics
import LeanTrominoes.Complexity.FiniteStateTransducerTime

/-! # Packing consecutive triples of binary words as block names -/
noncomputable section
namespace LeanTrominoes.BinaryWordTripleBlocks
open _root_.Computability Turing
open FiniteStateTransducer
abbrev Token := DelimitedBinaryWords.Token

def payload (token : Token) : List Token :=
  (BinaryWordBlocks.tokenBits token).map DelimitedBinaryWords.Token.bit

def next : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

def transition (index : Fin 3) : Token → Fin 3 × List Token
  | .wordStart => (index,(if index=0 then [.wordStart] else []) ++ payload .wordStart)
  | .bit b => (index,payload (.bit b))
  | .wordEnd => (next index,payload .wordEnd ++ (if index=2 then [.wordEnd] else []))

def tokens := FiniteStateTransducer.output (0 : Fin 3) transition (fun _ => [])

private theorem scan_bits (index : Fin 3) (bits : List Bool) :
    scan transition index (bits.map DelimitedBinaryWords.Token.bit) =
      (index,(bits.map DelimitedBinaryWords.Token.bit).flatMap payload) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [scan,transition,ih]

private theorem scan_word (index : Fin 3) (word : List Bool) :
    scan transition index (DelimitedBinaryWords.wordTokens word) =
      (next index,(if index=0 then [DelimitedBinaryWords.Token.wordStart] else []) ++
        (DelimitedBinaryWords.wordTokens word).flatMap payload ++
          (if index=2 then [DelimitedBinaryWords.Token.wordEnd] else [])) := by
  simp only [DelimitedBinaryWords.wordTokens,scan,transition]
  rw [scan_append,scan_bits]
  simp [scan,transition,List.append_assoc]

private theorem scan_triple (a b c : List Bool) :
    scan transition (0 : Fin 3) (DelimitedBinaryWords.encode ⟨[a,b,c]⟩) =
      (0,DelimitedBinaryWords.wordTokens (BinaryWordBlocks.pack [a,b,c])) := by
  simp only [DelimitedBinaryWords.encode,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,scan_append,scan_word]
  simp [next,BinaryWordBlocks.pack,DelimitedBinaryWords.encode,DelimitedBinaryWords.wordTokens,
    payload,List.map_flatMap,List.flatMap_append,List.append_assoc]
  rfl

private theorem scan_triples (triples : List (List Bool × List Bool × List Bool)) :
    scan transition (0 : Fin 3)
        (DelimitedBinaryWords.encode ⟨triples.flatMap fun triple => [triple.1,triple.2.1,triple.2.2]⟩) =
      (0,DelimitedBinaryWords.encode ⟨triples.map fun triple =>
        BinaryWordBlocks.pack [triple.1,triple.2.1,triple.2.2]⟩) := by
  induction triples with
  | nil => rfl
  | cons triple triples ih =>
    change scan transition 0 (DelimitedBinaryWords.encode
      ⟨[triple.1,triple.2.1,triple.2.2] ++ triples.flatMap (fun t => [t.1,t.2.1,t.2.2])⟩) = _
    have append (a b : List (List Bool)) :
        DelimitedBinaryWords.encode ⟨a++b⟩ =
          DelimitedBinaryWords.encode ⟨a⟩ ++ DelimitedBinaryWords.encode ⟨b⟩ := by
      simp [DelimitedBinaryWords.encode]
    rw [append,scan_append,scan_triple]
    dsimp only
    rw [ih]
    rfl

def input (triples : List (List Bool × List Bool × List Bool)) : DelimitedBinaryWords.Input :=
  ⟨triples.flatMap fun t => [t.1,t.2.1,t.2.2]⟩
def output (triples : List (List Bool × List Bool × List Bool)) : DelimitedBinaryWords.Input :=
  ⟨triples.map fun t => BinaryWordBlocks.pack [t.1,t.2.1,t.2.2]⟩

def computableInPolyTime :
    TM2ComputableInPolyTime (fun triples => DelimitedBinaryWords.encode (input triples))
      DelimitedBinaryWords.encode output := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    (fun triples => DelimitedBinaryWords.encode (input triples))
    (FiniteStateTransducer.computableInPolyTime (0 : Fin 3) transition (fun _ => []))
    (fun _ => rfl) (fun _ => rfl)
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared
  intro triples
  unfold FiniteStateTransducer.output
  rw [show DelimitedBinaryWords.encode (input triples)=
    DelimitedBinaryWords.encode ⟨triples.flatMap fun t => [t.1,t.2.1,t.2.2]⟩ from rfl,
    scan_triples]
  simp [output]

end LeanTrominoes.BinaryWordTripleBlocks
