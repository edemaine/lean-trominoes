/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatEncoding
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2ConstantValueCompiler

/-! # Binary natural fields as delimited bit words

A final empty word is retained as a harmless sentinel. This makes conversion
an unconditional finite block map, including on arbitrary raw input strings.
-/
noncomputable section
namespace LeanTrominoes.BinaryFieldWords
open Turing Computability
abbrev Symbol := PeriodicCNFFlatEncoding.Symbol

def bitSymbol (b : Bool) : Symbol := if b then .bit1 else .bit0

def prependBit (b : Bool) : List (List Bool) → List (List Bool)
  | [] => [[b]]
  | w::ws => (b::w)::ws

def readWords : List Symbol → List (List Bool)
  | [] => [[]]
  | .bit0::rest => prependBit false (readWords rest)
  | .bit1::rest => prependBit true (readWords rest)
  | .cons::rest => []::readWords rest
  | .consₗ::rest => []::readWords rest

def input (s : List Symbol) : DelimitedBinaryWords.Input := ⟨readWords s⟩

private def block : Symbol → List DelimitedBinaryWords.Token
  | .bit0 => [.bit false]
  | .bit1 => [.bit true]
  | .cons | .consₗ => [.wordEnd,.wordStart]

private theorem read_nonempty (s : List Symbol) : readWords s ≠ [] := by
  induction s with
  | nil => simp [readWords]
  | cons a s ih => cases a <;> cases h : readWords s <;> simp [readWords,prependBit,h]

private theorem encode_read (s : List Symbol) :
    DelimitedBinaryWords.encode (input s) = [.wordStart] ++ s.flatMap block ++ [.wordEnd] := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨w,ws,h⟩ := List.exists_cons_of_ne_nil (read_nonempty s)
    cases a <;> simp only [input,DelimitedBinaryWords.encode,readWords,h,prependBit,List.flatMap_cons,
      DelimitedBinaryWords.wordTokens,List.map_cons,List.map_nil,List.cons_append,List.nil_append,block] at ih ⊢ <;>
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.cons.injEq,
        true_and,eq_self] using ih

theorem read_field (bits : List Bool) (rest : List Symbol) :
    readWords (bits.map bitSymbol ++ .cons::rest) = bits::readWords rest := by
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [bitSymbol,readWords,prependBit,ih]

theorem read_fields (fields : List Nat) :
    readWords (PeriodicCNFFlatEncoding.encodeNatFields fields) = fields.map encodeNat ++ [[]] := by
  rw [PeriodicCNFFlatEncoding.encodeNatFields_eq_trList]
  induction fields with
  | nil => rfl
  | cons n ns ih =>
    change readWords (Turing.PartrecToTM2.trNat n ++ .cons :: Turing.PartrecToTM2.trList ns) = _
    have bits : Turing.PartrecToTM2.trNat n = (encodeNat n).map bitSymbol := by
      rw [Complexity.partrec_trNat_eq_map_encodeNat]
      apply List.map_congr_left
      intro b _
      cases b <;> rfl
    rw [bits,read_field,ih]
    rfl

def compiler : TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode input := by
  let physical := TM2ListAppend.computableInPolyTime
    (TM2ConstantValueCompiler.computableInPolyTime id id [DelimitedBinaryWords.Token.wordStart])
    (TM2ListAppend.computableInPolyTime (FiniteBlockTransducer.computableInPolyTime block)
      (TM2ConstantValueCompiler.computableInPolyTime id id [DelimitedBinaryWords.Token.wordEnd]))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  exact (encode_read s).symm.trans (by simp)

end LeanTrominoes.BinaryFieldWords
end
