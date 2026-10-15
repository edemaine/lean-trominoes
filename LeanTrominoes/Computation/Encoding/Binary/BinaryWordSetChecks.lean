/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Binary.BinaryWordTaggedPairs
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.Computation.Encoding.Aligned.AlignedBooleanListClosure
import Mathlib.Data.List.Nodup

/-! # Polynomial-time binary-word set verification

The machines check list inclusion and absence of duplicates using actual
word comparisons, square-row reshaping, and finite-state Boolean scans.
Words may be empty; neither list needs to have a fixed length.
-/
namespace LeanTrominoes.BinaryWordSetChecks
open Turing
abbrev Words := DelimitedBinaryWords.Input

def nodupCheck (input : Words) : Bool :=
  (DelimitedBinaryWordEqualitySquare.rows input).words.all
    (BinaryWordRowChecks.rowCheck .singleton)

theorem equalityRow_count (words : List (List Bool)) (word : List Bool) :
    (words.map fun other => decide (word=other)).count true=words.count word := by
  induction words with
  | nil => rfl
  | cons other words ih => by_cases same : word=other <;> simp_all [eq_comm]

theorem nodupCheck_correct (input : Words) :
    nodupCheck input=true ↔ input.words.Nodup := by
  rw [nodupCheck,DelimitedBinaryWordEqualitySquare.rows_words]
  simp only [LastRepresentativeEqualityRows.equalityRows,List.all_map,List.all_eq_true,
    Function.comp_def,BinaryWordRowChecks.singleton_correct,
    LastRepresentativeEqualityRows.equalityRow,equalityRow_count]
  exact List.nodup_iff_count_eq_one.symm

noncomputable def nodupComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      (fun bit : Bool => [bit]) nodupCheck := by
  letI : Inhabited DelimitedBinaryWords.finEncoding.Γ := ⟨DelimitedBinaryWords.Token.wordStart⟩
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.finEncoding.encode
    (FiniteBlockTransducer.computableInPolyTime (fun token => [token]))
    (fun _ => rfl) (fun _ => rfl)
  let words : TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode id :=
    TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical
      (fun input => by simp)
  let rows := DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode id words
  let checked := TM2CompositionMachine.computableInPolyTime rows
    (BinaryWordRowChecks.rowsComputableInPolyTime .singleton)
  let composed := TM2CompositionMachine.computableInPolyTime checked
    BinaryWordRowChecks.allComputableInPolyTime
  exact composed.of_eq (fun _ => by simp [nodupCheck,List.all_map])

def marked (input : Words × Words) : Words :=
  ⟨input.1.words.map (false :: ·) ++ input.2.words.map (true :: ·)⟩

def maskedRow (words : List (List Bool)) (word : List Bool) : List Bool :=
  words.map fun other => decide (word.tail=other.tail) && other.headD false

def maskedBits (input : Words) : List Bool :=
  input.words.flatMap (maskedRow input.words)

@[simp] theorem maskedBits_length (input : Words) :
    (maskedBits input).length=input.words.length^2 := by
  simp [maskedBits,maskedRow,pow_two]

def maskedSquare (input : Words) : BoolSquareRows.Input :=
  ⟨maskedBits input,by rw [maskedBits_length,Nat.sqrt_eq']⟩

def maskedRows (input : Words) : Words := (maskedSquare input).delimitedRows

theorem maskedRows_words (input : Words) :
    (maskedRows input).words=input.words.map (maskedRow input.words) := by
  have side : (maskedSquare input).side=input.words.length := by
    simp [BoolSquareRows.Input.side,maskedSquare]
  unfold maskedRows BoolSquareRows.Input.delimitedRows BoolSquareRows.Input.rows
    BoolSquareRows.Input.sizes
  rw [side]
  exact List.replicate_splitLengths_flatMap_of_length_eq input.words
    (maskedRow input.words) input.words.length (by intro; simp [maskedRow])

def subsetCheck (input : Words × Words) : Bool :=
  (maskedRows (marked input)).words.all (BinaryWordRowChecks.rowCheck .nonempty)

theorem maskedRow_marked (input : Words × Words) (word : List Bool) :
    true∈maskedRow (marked input).words word ↔ word.tail∈input.2.words := by
  simp [maskedRow,marked,List.mem_map]

theorem subsetCheck_correct (input : Words × Words) :
    subsetCheck input=true ↔ ∀ word∈input.1.words, word∈input.2.words := by
  rw [subsetCheck,maskedRows_words]
  simp only [List.all_map,List.all_eq_true,Function.comp_def,
    BinaryWordRowChecks.nonempty_correct,maskedRow_marked]
  constructor
  · intro h word member
    exact h (false::word) (by simp [marked,member])
  · intro h word member
    change word∈input.1.words.map (false::·) ++ input.2.words.map (true::·) at member
    rcases List.mem_append.mp member with query|value
    · obtain ⟨original,hm,rfl⟩ := List.mem_map.mp query
      exact h original hm
    · obtain ⟨original,hm,rfl⟩ := List.mem_map.mp value
      exact hm

theorem maskedBits_eq (input : Words) :
    List.zipWith Bool.and
      (DelimitedBinaryWordPairs.equalities
        (BinaryWordTaggedPairs.erased (DelimitedBinaryWordPairProductMachine.pairs input)))
      (BinaryWordTaggedPairs.flags (DelimitedBinaryWordPairProductMachine.pairs input))=
      maskedBits input := by
  have combine (pairs : List (List Bool × List Bool)) :
      List.zipWith Bool.and
        (pairs.map fun pair => decide (pair.1.tail=pair.2.tail))
        (pairs.map fun pair => pair.2.headD false)=
        pairs.map (fun pair => decide (pair.1.tail=pair.2.tail) && pair.2.headD false) := by
    induction pairs with
    | nil => rfl
    | cons pair pairs ih => simp
  simp only [DelimitedBinaryWordPairs.equalities,BinaryWordTaggedPairs.erased,
    List.map_map,Function.comp_def,BinaryWordTaggedPairs.flags]
  rw [combine]
  simp only [DelimitedBinaryWordPairProductMachine.pairs,maskedBits,List.map_flatMap,
    List.map_map,Function.comp_def]
  rfl

/-- A tagged equality square, masked to count only the designated columns. -/
noncomputable def maskedBitsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id maskedBits := by
  let compared := TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      DelimitedBinaryWordPairProductMachine.computableInPolyTime
      BinaryWordTaggedPairs.erasedComputableInPolyTime)
    DelimitedBinaryWordPairEqualityMachine.computableInPolyTime
  let flags := TM2CompositionMachine.computableInPolyTime
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
    BinaryWordTaggedPairs.flagsComputableInPolyTime
  letI : Inhabited DelimitedBinaryWords.finEncoding.Γ := ⟨DelimitedBinaryWords.Token.wordStart⟩
  let combined := AlignedBooleanListClosure.combinedComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode .conjunction _ _
    (fun input => by simp [DelimitedBinaryWordPairs.equalities,
      BinaryWordTaggedPairs.erased,BinaryWordTaggedPairs.flags]) compared flags
  exact combined.of_eq maskedBits_eq

noncomputable def maskedRowsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode maskedRows := by
  let square : TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      BoolSquareRows.finEncoding.encode maskedSquare :=
    TM2PolyTimeOutputEncodingTransport.of_identity_output_eq maskedBitsComputableInPolyTime
      (fun _ => rfl)
  let composed := TM2CompositionMachine.computableInPolyTime square BoolSquareRowsMachine.computableInPolyTime
  exact composed.of_eq (fun _ => rfl)

abbrev PairToken := SeparatedProductEncoding.Token DelimitedBinaryWords.Token DelimitedBinaryWords.Token

def markBlock : PairToken → List DelimitedBinaryWords.Token
  | .left .wordStart => [.wordStart,.bit false]
  | .right .wordStart => [.wordStart,.bit true]
  | .left token | .right token => [token]
  | .separator => []

theorem mark_word (left : Bool) (word : List Bool) :
    ((DelimitedBinaryWords.wordTokens word).map
      (if left then SeparatedProductEncoding.Token.left else SeparatedProductEncoding.Token.right)).flatMap markBlock=
      DelimitedBinaryWords.wordTokens ((!left)::word) := by
  have mapBits (tag : DelimitedBinaryWords.Token → PairToken)
      (eq : tag=SeparatedProductEncoding.Token.left ∨ tag=SeparatedProductEncoding.Token.right) :
      ((word.map DelimitedBinaryWords.Token.bit).map tag).flatMap markBlock=
        word.map DelimitedBinaryWords.Token.bit := by
    rcases eq with rfl|rfl <;> induction word <;> simp_all [markBlock]
  cases left <;>
    simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
      DelimitedBinaryWords.wordTokens,List.map_cons,List.map_append,List.flatMap_cons,
      List.flatMap_append]
  · rw [mapBits _ (Or.inr rfl)]
    rfl
  · rw [mapBits _ (Or.inl rfl)]
    rfl

theorem mark_encode (input : Words × Words) :
    (SeparatedProductEncoding.encode DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode input).flatMap markBlock=
      DelimitedBinaryWords.finEncoding.encode (marked input) := by
  have blocks (tag : DelimitedBinaryWords.Token → PairToken) (left : Bool)
      (eq : tag=if left then SeparatedProductEncoding.Token.left else SeparatedProductEncoding.Token.right) (words : List (List Bool)) :
      ((words.flatMap DelimitedBinaryWords.wordTokens).map tag).flatMap markBlock=
        (words.map ((!left)::·)).flatMap DelimitedBinaryWords.wordTokens := by
    subst tag
    simp only [List.map_flatMap,List.flatMap_assoc,List.flatMap_map]
    exact List.flatMap_congr (fun word _ => by simpa only [List.flatMap_map] using mark_word left word)
  change ((DelimitedBinaryWords.encode input.1).map SeparatedProductEncoding.Token.left ++
    SeparatedProductEncoding.Token.separator :: (DelimitedBinaryWords.encode input.2).map
      SeparatedProductEncoding.Token.right).flatMap markBlock = DelimitedBinaryWords.encode (marked input)
  rw [List.flatMap_append,List.flatMap_cons]
  change ((input.1.words.flatMap DelimitedBinaryWords.wordTokens).map
    SeparatedProductEncoding.Token.left).flatMap markBlock ++
      ([] ++ ((input.2.words.flatMap DelimitedBinaryWords.wordTokens).map
        SeparatedProductEncoding.Token.right).flatMap markBlock) = DelimitedBinaryWords.encode (marked input)
  rw [blocks SeparatedProductEncoding.Token.left true rfl,
    blocks SeparatedProductEncoding.Token.right false rfl]
  simp [DelimitedBinaryWords.encode,marked]

noncomputable def markedComputableInPolyTime :
    TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode DelimitedBinaryWords.finEncoding.encode DelimitedBinaryWords.finEncoding.encode)
      DelimitedBinaryWords.finEncoding.encode marked := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare
    (SeparatedProductEncoding.encode DelimitedBinaryWords.finEncoding.encode DelimitedBinaryWords.finEncoding.encode)
    (FiniteBlockTransducer.computableInPolyTime markBlock) (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical mark_encode

noncomputable def subsetComputableInPolyTime :
    TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode DelimitedBinaryWords.finEncoding.encode DelimitedBinaryWords.finEncoding.encode)
      (fun bit : Bool => [bit]) subsetCheck := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (TM2CompositionMachine.computableInPolyTime markedComputableInPolyTime maskedRowsComputableInPolyTime)
      (BinaryWordRowChecks.rowsComputableInPolyTime .nonempty))
    BinaryWordRowChecks.allComputableInPolyTime
  exact composed.of_eq (fun _ => by simp [subsetCheck,List.all_map])

end LeanTrominoes.BinaryWordSetChecks
