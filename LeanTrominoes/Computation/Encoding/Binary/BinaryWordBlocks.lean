/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Binary.BinaryWordRowChecks

/-! # Packing lists of binary words into selectable blocks

Two bits encode each word delimiter or data bit. An entire tile footprint
can therefore be selected by one certificate bit, then unpacked by a
finite-state machine into its constituent cell names.
-/
namespace LeanTrominoes.BinaryWordBlocks
open Turing
abbrev Token := DelimitedBinaryWords.Token

def tokenBits : Token → List Bool
  | .wordStart => [false,false]
  | .bit false => [false,true]
  | .bit true => [true,false]
  | .wordEnd => [true,true]

def pairToken : Bool → Bool → Token
  | false,false => .wordStart
  | false,true => .bit false
  | true,false => .bit true
  | true,true => .wordEnd

def pack (words : List (List Bool)) : List Bool :=
  (DelimitedBinaryWords.encode ⟨words⟩).flatMap tokenBits

def transition (first : Option Bool) : Token → Option Bool × List Token
  | .wordStart | .wordEnd => (none,[])
  | .bit bit => match first with
    | none => (some bit,[])
    | some prior => (none,[pairToken prior bit])

theorem scan_token (token : Token) :
    FiniteStateTransducer.scan transition none ((tokenBits token).map DelimitedBinaryWords.Token.bit)=
      (none,[token]) := by
  cases token with
  | wordStart => rfl
  | wordEnd => rfl
  | bit bit => cases bit <;> rfl

theorem scan_tokens (tokens : List Token) :
    FiniteStateTransducer.scan transition none
      ((tokens.flatMap tokenBits).map DelimitedBinaryWords.Token.bit)=(none,tokens) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.flatMap_cons,List.map_append]
    rw [FiniteStateTransducer.scan_append,scan_token]
    simp [ih]

theorem scan_block (first : Option Bool) (words : List (List Bool)) :
    FiniteStateTransducer.scan transition first
      (DelimitedBinaryWords.wordTokens (pack words))=
      (none,DelimitedBinaryWords.encode ⟨words⟩) := by
  simp only [DelimitedBinaryWords.wordTokens,FiniteStateTransducer.scan,transition]
  rw [FiniteStateTransducer.scan_append]
  unfold pack
  rw [scan_tokens]
  simp [FiniteStateTransducer.scan,transition]

theorem pack_injective : Function.Injective pack := by
  intro first second equal
  have scanned := congrArg (fun bits =>
    (FiniteStateTransducer.scan transition none
      (DelimitedBinaryWords.wordTokens bits)).2) equal
  simp only [scan_block] at scanned
  have decoded := DelimitedBinaryWords.finEncoding.encoding.encode_injective scanned
  exact congrArg DelimitedBinaryWords.Input.words decoded

theorem scan_blocks (first : Option Bool) (blocks : List (List (List Bool))) :
    (FiniteStateTransducer.scan transition first
      (DelimitedBinaryWords.encode ⟨blocks.map pack⟩)).2=
      DelimitedBinaryWords.encode ⟨blocks.flatten⟩ := by
  induction blocks generalizing first with
  | nil => rfl
  | cons block blocks ih =>
    simp only [DelimitedBinaryWords.encode,List.map_cons,List.flatMap_cons]
    rw [FiniteStateTransducer.scan_append,scan_block]
    change DelimitedBinaryWords.encode ⟨block⟩ ++
      (FiniteStateTransducer.scan transition none
        (DelimitedBinaryWords.encode ⟨blocks.map pack⟩)).2 = _
    rw [ih]
    simp [DelimitedBinaryWords.encode]

/-- Unpacking a sequence of complete footprint blocks is linear time in
the physical input length. -/
noncomputable def flattenComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun blocks : List (List (List Bool)) => DelimitedBinaryWords.encode ⟨blocks.map pack⟩)
      DelimitedBinaryWords.finEncoding.encode
      (fun blocks => (⟨blocks.flatten⟩ : DelimitedBinaryWords.Input)) := by
  let physical := FiniteStateTransducer.computableInPolyTime none transition (fun _ => [])
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    (fun blocks : List (List (List Bool)) => DelimitedBinaryWords.encode ⟨blocks.map pack⟩)
    physical (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared
    (fun blocks => by simp [FiniteStateTransducer.output,scan_blocks])

@[simp] theorem pack_length (words : List (List Bool)) :
    (pack words).length=2*(DelimitedBinaryWords.encode ⟨words⟩).length := by
  have length (tokens : List Token) : (tokens.flatMap tokenBits).length=2*tokens.length := by
    induction tokens with
    | nil => rfl
    | cons token tokens ih => cases token with
      | wordStart => simp [tokenBits,ih]; omega
      | wordEnd => simp [tokenBits,ih]; omega
      | bit bit => cases bit <;> simp [tokenBits,ih] <;> omega
  exact length _

end LeanTrominoes.BinaryWordBlocks
