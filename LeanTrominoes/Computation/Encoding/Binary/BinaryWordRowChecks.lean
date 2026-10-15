/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteStateTransducerTime
import LeanTrominoes.Complexity.FiniteStateTransducerSemantics
import LeanTrominoes.Computation.TM2.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.Computation.TM2.TM2ComputableInPolyTimeCongr
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedBinaryWords

/-! # Polynomial-time Boolean row checks

Finite control suffices to test whether each delimited Boolean row contains
at least one true bit, or exactly one. No numeric counters are needed.
-/
namespace LeanTrominoes.BinaryWordRowChecks
open Turing
abbrev Token := DelimitedBinaryWords.Token

inductive Count
  | zero | one | many
  deriving DecidableEq, Fintype

def Count.add : Count → Bool → Count
  | count, false => count
  | .zero, true => .one
  | _, true => .many

inductive Test
  | nonempty | singleton
  deriving DecidableEq, Fintype

def Test.accept : Test → Count → Bool
  | .nonempty, .zero => false
  | .nonempty, _ => true
  | .singleton, .one => true
  | .singleton, _ => false

def rowCount (bits : List Bool) : Count := bits.foldl Count.add .zero

def rowCheck (test : Test) (bits : List Bool) : Bool := test.accept (rowCount bits)

theorem fold_count (count : Count) (bits : List Bool) :
    bits.foldl Count.add count =
      match count with
      | .zero => if bits.count true=0 then .zero else if bits.count true=1 then .one else .many
      | .one => if bits.count true=0 then .one else .many
      | .many => .many := by
  induction bits generalizing count with
  | nil => cases count <;> simp
  | cons bit bits ih =>
    cases bit <;> cases count <;>
      simp [List.foldl_cons,Count.add,ih]

theorem nonempty_correct (bits : List Bool) :
    rowCheck .nonempty bits=true ↔ true∈bits := by
  simp only [rowCheck,rowCount,fold_count]
  split_ifs <;> simp_all [Test.accept,List.count_eq_zero]
  exact List.count_pos_iff.mp (by omega)

theorem singleton_correct (bits : List Bool) :
    rowCheck .singleton bits=true ↔ bits.count true=1 := by
  simp only [rowCheck,rowCount,fold_count]
  split_ifs <;> simp_all [Test.accept]

def transition (test : Test) (count : Count) : Token → Count × List Bool
  | .wordStart => (.zero,[])
  | .bit bit => (count.add bit,[])
  | .wordEnd => (.zero,[test.accept count])

theorem scan_bits (test : Test) (count : Count) (bits : List Bool) :
    FiniteStateTransducer.scan (transition test) count (bits.map .bit)=
      (bits.foldl Count.add count,[]) := by
  induction bits generalizing count with
  | nil => rfl
  | cons bit bits ih => simp [FiniteStateTransducer.scan,transition,ih]

theorem scan_word (test : Test) (count : Count) (bits : List Bool) :
    FiniteStateTransducer.scan (transition test) count
      (DelimitedBinaryWords.wordTokens bits)=(.zero,[rowCheck test bits]) := by
  simp only [DelimitedBinaryWords.wordTokens,FiniteStateTransducer.scan,transition]
  rw [FiniteStateTransducer.scan_append,scan_bits]
  rfl

theorem scan_rows (test : Test) (count : Count) (words : List (List Bool)) :
    (FiniteStateTransducer.scan (transition test) count
      (words.flatMap DelimitedBinaryWords.wordTokens)).2=words.map (rowCheck test) := by
  induction words generalizing count with
  | nil => rfl
  | cons word words ih =>
    rw [List.flatMap_cons,FiniteStateTransducer.scan_append,scan_word]
    simp [ih]

noncomputable def rowsComputableInPolyTime (test : Test) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (fun input => input.words.map (rowCheck test)) := by
  let physical := FiniteStateTransducer.computableInPolyTime
    .zero (transition test) (fun _ => [])
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.finEncoding.encode physical (fun _ => rfl)
    (fun input => by simp [FiniteStateTransducer.output,scan_rows,DelimitedBinaryWords.encode])

def allTransition (prior : Bool) (bit : Bool) : Bool × List Bool := (prior && bit,[])

theorem all_scan (prior : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan allTransition prior bits=(prior && bits.all id,[]) := by
  induction bits generalizing prior with
  | nil => simp [FiniteStateTransducer.scan]
  | cons bit bits ih => simp [FiniteStateTransducer.scan,allTransition,ih,Bool.and_assoc]

noncomputable def allComputableInPolyTime :
    TM2ComputableInPolyTime id (fun bit : Bool => [bit]) (fun bits => bits.all id) := by
  let physical := FiniteStateTransducer.computableInPolyTime true allTransition (fun bit => [bit])
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical
    (fun bits => by simp [FiniteStateTransducer.output,all_scan])

end LeanTrominoes.BinaryWordRowChecks
