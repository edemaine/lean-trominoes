/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Binary.BinaryWordRowChecks
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedBinaryWordPairs

/-! # Finite-state operations on tagged binary-word pairs

A leading Boolean tag identifies a word's role. The equality machine sees
the remaining bits; a separate scan recovers the second word's tag.
-/
namespace LeanTrominoes.BinaryWordTaggedPairs
open Turing
abbrev Token := DelimitedBinaryWordPairs.Token

def eraseTransition (atStart : Bool) : Token → Bool × List Token
  | .pairStart => (true,[.pairStart])
  | .middle => (true,[.middle])
  | .firstBit bit => (false,if atStart then [] else [.firstBit bit])
  | .secondBit bit => (false,if atStart then [] else [.secondBit bit])
  | .pairEnd => (true,[.pairEnd])

theorem erase_bits (constructor : Bool → Token)
    (kind : constructor=DelimitedBinaryWordPairs.Token.firstBit ∨ constructor=DelimitedBinaryWordPairs.Token.secondBit)
    (atStart : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan eraseTransition atStart (bits.map constructor)=
      (if bits=[] then atStart else false,
        (if atStart then bits.tail else bits).map constructor) := by
  induction bits generalizing atStart with
  | nil => simp [FiniteStateTransducer.scan]
  | cons bit bits ih =>
    rcases kind with rfl|rfl <;> cases atStart <;>
      simp [FiniteStateTransducer.scan,eraseTransition,ih]

theorem erase_pair (atStart : Bool) (pair : List Bool × List Bool) :
    FiniteStateTransducer.scan eraseTransition atStart
      (DelimitedBinaryWordPairs.pairTokens pair)=
      (true,DelimitedBinaryWordPairs.pairTokens (pair.1.tail,pair.2.tail)) := by
  simp only [DelimitedBinaryWordPairs.pairTokens,FiniteStateTransducer.scan,eraseTransition]
  rw [FiniteStateTransducer.scan_append,erase_bits _ (Or.inl rfl)]
  simp only
  simp only [FiniteStateTransducer.scan,eraseTransition]
  rw [FiniteStateTransducer.scan_append,erase_bits _ (Or.inr rfl)]
  simp [FiniteStateTransducer.scan,eraseTransition]

def erased (input : DelimitedBinaryWordPairs.Input) : DelimitedBinaryWordPairs.Input :=
  ⟨input.pairs.map fun pair => (pair.1.tail,pair.2.tail)⟩

theorem erase_pairs (atStart : Bool) (pairs : List (List Bool × List Bool)) :
    (FiniteStateTransducer.scan eraseTransition atStart
      (pairs.flatMap DelimitedBinaryWordPairs.pairTokens)).2=
      (pairs.map fun pair => (pair.1.tail,pair.2.tail)).flatMap DelimitedBinaryWordPairs.pairTokens := by
  induction pairs generalizing atStart with
  | nil => rfl
  | cons pair pairs ih =>
    rw [List.flatMap_cons,FiniteStateTransducer.scan_append,erase_pair]
    simp [ih]

noncomputable def erasedComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWordPairs.finEncoding.encode
      DelimitedBinaryWordPairs.finEncoding.encode erased := by
  let physical := FiniteStateTransducer.computableInPolyTime true eraseTransition (fun _ => [])
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWordPairs.finEncoding.encode physical (fun _ => rfl)
    (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared
    (fun input => by simp [FiniteStateTransducer.output,erase_pairs,
      DelimitedBinaryWordPairs.encode,erased])

def flagTransition (flag : Option Bool) : Token → Option Bool × List Bool
  | .pairStart | .middle => (none,[])
  | .firstBit _ => (flag,[])
  | .secondBit bit => (some (flag.getD bit),[])
  | .pairEnd => (none,[flag.getD false])

theorem flag_firstBits (flag : Option Bool) (bits : List Bool) :
    FiniteStateTransducer.scan flagTransition flag (bits.map DelimitedBinaryWordPairs.Token.firstBit)=(flag,[]) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [FiniteStateTransducer.scan,flagTransition,ih]

theorem flag_secondBits (flag : Option Bool) (bits : List Bool) :
    FiniteStateTransducer.scan flagTransition flag (bits.map DelimitedBinaryWordPairs.Token.secondBit)=
      (flag.or bits.head?,[]) := by
  induction bits generalizing flag with
  | nil => cases flag <;> rfl
  | cons bit bits ih =>
    cases flag <;> simp [FiniteStateTransducer.scan,flagTransition,ih]

theorem flag_pair (flag : Option Bool) (pair : List Bool × List Bool) :
    FiniteStateTransducer.scan flagTransition flag
      (DelimitedBinaryWordPairs.pairTokens pair)=
      (none,[pair.2.headD false]) := by
  simp only [DelimitedBinaryWordPairs.pairTokens,FiniteStateTransducer.scan,flagTransition]
  rw [FiniteStateTransducer.scan_append,flag_firstBits]
  simp only
  simp only [FiniteStateTransducer.scan,flagTransition]
  rw [FiniteStateTransducer.scan_append,flag_secondBits]
  simp only [FiniteStateTransducer.scan,flagTransition]
  cases pair.2 <;> rfl

def flags (input : DelimitedBinaryWordPairs.Input) : List Bool :=
  input.pairs.map fun pair => pair.2.headD false

theorem flag_pairs (flag : Option Bool) (pairs : List (List Bool × List Bool)) :
    (FiniteStateTransducer.scan flagTransition flag
      (pairs.flatMap DelimitedBinaryWordPairs.pairTokens)).2=
      pairs.map (fun pair => pair.2.headD false) := by
  induction pairs generalizing flag with
  | nil => rfl
  | cons pair pairs ih =>
    rw [List.flatMap_cons,FiniteStateTransducer.scan_append,flag_pair]
    simp [ih]

noncomputable def flagsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWordPairs.finEncoding.encode id flags := by
  let physical := FiniteStateTransducer.computableInPolyTime none flagTransition (fun _ => [])
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWordPairs.finEncoding.encode physical (fun _ => rfl)
    (fun input => by simp [FiniteStateTransducer.output,flag_pairs,
      DelimitedBinaryWordPairs.encode,flags])

end LeanTrominoes.BinaryWordTaggedPairs
