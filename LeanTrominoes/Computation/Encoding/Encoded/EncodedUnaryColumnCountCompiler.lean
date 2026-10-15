/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Encoded.EncodedUnaryColumnCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldEqualityRowsCompiler
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedBinaryWordTrueCountCompiler

/-! # Counting occurrences of compiled unary keys -/
noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

def occurrenceCounts (values : List Nat) : List Nat := values.map fun n => values.count n

theorem equalityWord_trueCount (values : List Nat) (key : Nat) :
    (values.map fun value => decide (UnaryFieldBinaryWords.word key=UnaryFieldBinaryWords.word value)).count true =
      values.count key := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    by_cases same : key=value
    · subst value
      simp [ih]
    · have different : UnaryFieldBinaryWords.word key ≠ UnaryFieldBinaryWords.word value := by
        intro equal
        have length := congrArg List.length equal
        exact same (by simpa [UnaryFieldBinaryWords.word] using length)
      simp [different,Ne.symm same,ih]

def occurrenceCountsCompiler : TM2ComputableInPolyTime unaryFields unaryFields occurrenceCounts := by
  let words := UnaryFieldBinaryWords.wordsComputableInPolyTime
  let rows := DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime unaryFields UnaryFieldBinaryWords.words words
  let physical := TM2CompositionMachine.computableInPolyTime rows DelimitedBinaryWordTrueCounts.computableInPolyTime
  apply TM2ComputableInPolyTime.of_eq physical
  intro values
  simp only [DelimitedBinaryWordTrueCounts.counts,DelimitedBinaryWordEqualitySquare.rows_words,
    UnaryFieldBinaryWords.words,LastRepresentativeEqualityRows.equalityRows,
    occurrenceCounts,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro key _
  simpa only [DelimitedBinaryWordTrueCounts.countTrue,LastRepresentativeEqualityRows.equalityRow,
    List.map_map,Function.comp_def] using equalityWord_trueCount values key

variable {Input Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
  {encodeInput : Input → List Symbol} {rows : Input → List Row} {query : Input → Row → Nat}
  {values : Input → List Nat}

def countsOfValues (queries : Compiler encodeInput rows query)
    (table : TM2ComputableInPolyTime encodeInput unaryFields values)
    (unique : ∀ s, ((rows s).map (query s)).Nodup) :
    Compiler encodeInput rows (fun s row => (values s).count (query s row)) := by
  let combined := fun s => values s ++ (rows s).map (query s)
  let keys : Compiler encodeInput combined (fun _ n => n) := by
    let physical := UnaryFieldClosure.appendCompiler encodeInput _ _ table queries
    exact TM2ComputableInPolyTime.of_eq physical (fun s => by simp [combined])
  let counts : Compiler encodeInput combined (fun s n => (combined s).count n) := by
    let physical := TM2CompositionMachine.computableInPolyTime keys occurrenceCountsCompiler
    exact TM2ComputableInPolyTime.of_eq physical (fun s => by simp [occurrenceCounts])
  let found := keyed queries keys counts (fun s n => (combined s).count n)
    (fun _ _ _ => rfl) (fun s row member =>
      ⟨query s row,List.mem_append_right _ (List.mem_map.mpr ⟨row,member,rfl⟩),rfl⟩)
  let physical := sub found (constant found 1)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row member
  have once : ((rows s).map (query s)).count (query s row)=1 :=
    List.count_eq_one_of_mem (unique s) (List.mem_map.mpr ⟨row,member,rfl⟩)
  simp [combined,List.count_append,once]

end LeanTrominoes.EncodedUnaryColumn
end
