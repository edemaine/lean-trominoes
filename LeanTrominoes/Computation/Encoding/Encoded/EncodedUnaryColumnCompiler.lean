/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnPairCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnDedupCompiler

/-! # Unary arithmetic compiled from arbitrary finite input encodings

These closures retain the source encoding throughout composition. In particular,
a structured coordinate input need not first be decoded by an unverified function.
-/
noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Input Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {encodeInput : Input → List Symbol}

abbrev Compiler (encodeInput : Input → List Symbol)
    (rows : Input → List Index) (value : Input → Index → Nat) :=
  TM2ComputableInPolyTime encodeInput unaryFields (fun s => (rows s).map (value s))

abbrev ScalarCompiler (encodeInput : Input → List Symbol) (n : Input → Nat) :=
  TM2ComputableInPolyTime encodeInput unaryFields (fun s => [n s])

private def alignedPairs (first second : Input → List Nat)
    (aligned : ∀ s, (first s).length = (second s).length)
    (a : TM2ComputableInPolyTime encodeInput unaryFields first)
    (b : TM2ComputableInPolyTime encodeInput unaryFields second) :
    TM2ComputableInPolyTime encodeInput DelimitedBinaryWordPairs.encode
      (fun s => UnaryAlignedWordPairs.input (first s) (second s)) := by
  let interleaved := AlignedUnaryListClosure.addedComputableInPolyTime encodeInput
    (fun s => UnaryFieldAlternatingPadding.appendZeroValues (first s))
    (fun s => UnaryFieldAlternatingPadding.prependZeroValues (second s))
    (fun s => by simp [aligned s])
    (TM2CompositionMachine.computableInPolyTime a
      UnaryFieldAlternatingPadding.appendZeroValuesComputableInPolyTime)
    (TM2CompositionMachine.computableInPolyTime b
      UnaryFieldAlternatingPadding.prependZeroValuesComputableInPolyTime)
  let encoded : TM2ComputableInPolyTime unaryFields id
      (fun values => UnaryAlignedWordPairs.tokens (unaryFields values)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
      (FiniteStateTransducer.computableInPolyTime UnaryAlignedWordPairs.Control.start
        UnaryAlignedWordPairs.transition UnaryAlignedWordPairs.finish)
      (fun _ => rfl) (fun _ => rfl)
  let result := TM2CompositionMachine.computableInPolyTime interleaved encoded
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  change UnaryAlignedWordPairs.tokens (unaryFields
    (AlignedUnaryBooleanChoice.candidateValues (first s) (second s))) = _
  rw [AlignedUnaryBooleanChoice.candidateValues_eq_interleaved,
    UnaryAlignedWordPairs.tokens_interleaved]

variable {rows : Input → List Index} {f g : Input → Index → Nat} {n : Input → Nat}
def residue (c : Compiler encodeInput rows f) (m : Nat) (positive : 0 < m) (table : Fin m → Nat) :
    Compiler encodeInput rows (fun s i => table ⟨f s i % m,Nat.mod_lt _ positive⟩) := by
  let result := TM2CompositionMachine.computableInPolyTime c
    (UnaryFieldResidue.computableInPolyTime m positive table)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by simp [List.map_map]))

def constant (c : Compiler encodeInput rows f) (n : Nat) : Compiler encodeInput rows (fun _ _ => n) := by
  exact residue c 1 (by decide) (fun _ => n)

def scale (c : Compiler encodeInput rows f) (n : Nat) : Compiler encodeInput rows (fun s i => f s i*n) := by
  let result := TM2CompositionMachine.computableInPolyTime c (UnaryFieldConstantScale.computableInPolyTime n)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by simp [UnaryFieldConstantScale.values,List.map_map]))

def halve (c : Compiler encodeInput rows f) : Compiler encodeInput rows (fun s i => f s i/2) := by
  let result := TM2CompositionMachine.computableInPolyTime c UnaryFieldHalve.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by simp [List.map_map]))

def divPowTwo (c : Compiler encodeInput rows f) : (k : Nat) → Compiler encodeInput rows (fun s i => f s i/2^k)
  | 0 => TM2ComputableInPolyTime.of_eq c (by intro s; simp)
  | k+1 => TM2ComputableInPolyTime.of_eq (halve (divPowTwo c k)) (by
      intro s
      simp [Nat.div_div_eq_div_mul,Nat.pow_succ])

def add (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g) : Compiler encodeInput rows (fun s i => f s i+g s i) := by
  let result := AlignedUnaryListClosure.addedComputableInPolyTime encodeInput _ _ (fun s => by simp) a b
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (UnaryAlignedAddMachine.sums_map _ _ _))

def sub (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g) : Compiler encodeInput rows (fun s i => f s i-g s i) := by
  let result := TM2CompositionMachine.computableInPolyTime
    (alignedPairs _ _ (fun s => by simp) a b)
    (DelimitedBinaryWordPairExcessMachine.computableInPolyTime true)
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  change UnaryAlignedDifference.values true _ _ = _
  rw [UnaryAlignedDifference.values_eq_zipWith]
  simp only [↓reduceIte,List.zipWith_map]
  induction rows s with
  | nil => rfl
  | cons i rest ih => simp [ih]

def lookup (c : Compiler encodeInput rows f) (table : List Nat)
    (bounded : ∀ s i, i ∈ rows s → f s i < table.length) :
    Compiler encodeInput rows (fun s i => table[f s i]?.getD 0) := by
  let result := UnaryIndexedValueLookup.valuesComputableInPolyTime encodeInput _ (fun _ => table) c
    (TM2ConstantValueCompiler.computableInPolyTime encodeInput unaryFields table)
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    exact bounded s i hi)]
  simp [List.map_map]

def cartesianLeft {Other : Type} {other : Input → List Other}
    {value : Input → Other → Nat} (a : Compiler encodeInput rows f) (b : Compiler encodeInput other value) :
    Compiler encodeInput (fun s => (rows s).flatMap fun i => (other s).map fun j => (i,j))
      (fun s p => f s p.1) := by
  let result := UnaryFieldCartesian.computableInPolyTime encodeInput _ _ a b .first
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by
      simp [UnaryFieldSquareProjection.choose,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]))

def cartesianRight {Other : Type} {other : Input → List Other}
    {value : Input → Other → Nat} (a : Compiler encodeInput rows f) (b : Compiler encodeInput other value) :
    Compiler encodeInput (fun s => (rows s).flatMap fun i => (other s).map fun j => (i,j))
      (fun s p => value s p.2) := by
  let result := UnaryFieldCartesian.computableInPolyTime encodeInput _ _ a b .second
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by
      simp [UnaryFieldSquareProjection.choose,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]))
def naturalRange (c : ScalarCompiler encodeInput n) : Compiler encodeInput (fun s => List.range (n s)) (fun _ i => i) := by
  let scalar : TM2ComputableInPolyTime encodeInput (fun n => unaryFields [n]) n :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq c (fun _ => rfl)
  let result := TM2CompositionMachine.computableInPolyTime scalar UnaryNaturalRange.computableInPolyTime
  exact TM2ComputableInPolyTime.of_eq result (fun s => by simp)

def broadcast (c : Compiler encodeInput rows f) (scalar : ScalarCompiler encodeInput n) : Compiler encodeInput rows (fun s _ => n s) := by
  let result := UnaryIndexedValueLookup.valuesComputableInPolyTime encodeInput _ _ (constant c 0) scalar
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by simp)]
  simp

def multiplyScalar (c : Compiler encodeInput rows f) (scalar : ScalarCompiler encodeInput n) :
    Compiler encodeInput rows (fun s i => f s i*n s) := by
  let result := UnaryFieldScalarMultiply.computableInPolyTime encodeInput n _ scalar c
  exact TM2ComputableInPolyTime.of_eq result (fun s => by simp [List.map_map])

def keyed {Other : Type} {candidates : Input → List Other}
    {key value : Input → Other → Nat} (queries : Compiler encodeInput rows f)
    (keys : Compiler encodeInput candidates key) (values : Compiler encodeInput candidates value)
    (datum : Input → Nat → Nat)
    (correct : ∀ s i, i ∈ candidates s → value s i = datum s (key s i))
    (present : ∀ s i, i ∈ rows s → ∃ j ∈ candidates s, key s j = f s i) :
    Compiler encodeInput rows (fun s i => datum s (f s i)) := by
  let result := UnaryKeyedValueLookup.valuesComputableInPolyTime encodeInput _ _ _ (fun s => by simp) queries keys values
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [UnaryKeyedValueLookup.values_eq_map_datum _ _ _ (datum s) (by
    rw [List.map_map]
    exact List.map_congr_left (correct s)) (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    obtain ⟨j,hj,eq⟩ := present s i hi
    exact List.mem_map.mpr ⟨j,hj,eq⟩)]
  simp [List.map_map]
def columnBound (queries : Compiler encodeInput rows f) :
    ScalarCompiler encodeInput (fun s => ((rows s).map (f s)).sum + 1) := by
  let total : ScalarCompiler encodeInput (fun s => ((rows s).map (f s)).sum) :=
    TM2CompositionMachine.computableInPolyTime queries UnaryFieldAggregate.sumCompiler
  let column : Compiler encodeInput (fun _ : Input => [()])
      (fun s _ => ((rows s).map (f s)).sum) := total
  exact add column (constant column 1)

/-- The computed unary bound makes the square table polynomial in the input. -/
def square (queries : Compiler encodeInput rows f) : Compiler encodeInput rows (fun s i => f s i*f s i) := by
  let bound := columnBound queries
  let keys := naturalRange bound
  let odds := add (scale keys 2) (constant keys 1)
  let raw := TM2CompositionMachine.computableInPolyTime odds
    UnaryPrefixSumsMachine.computableInPolyTime
  let squares : Compiler encodeInput (fun s => List.range (((rows s).map (f s)).sum+1))
      (fun _ i => i*i) := TM2ComputableInPolyTime.of_eq raw (fun s => UnaryColumn.starts_odds _)
  apply keyed queries keys squares (fun _ n => n*n)
  · intro s i _; rfl
  · intro s i hi
    refine ⟨f s i,List.mem_range.mpr ?_,rfl⟩
    have le := List.le_sum_of_mem (List.mem_map.mpr ⟨i,hi,rfl⟩ :
      f s i ∈ (rows s).map (f s))
    omega

theorem product_from_squares (a b : Nat) :
    ((a+b)*(a+b)-a*a-b*b)/2=a*b := by
  have eq : (a+b)*(a+b)=a*a+b*b+(a*b)*2 := by ring
  rw [eq]
  have sub : a*a+b*b+a*b*2-a*a-b*b=a*b*2 := by omega
  rw [sub,Nat.mul_div_left _ (by decide : 0 < 2)]

/-- Pointwise products preserve row order, including empty and repeated rows. -/
def multiply (first : Compiler encodeInput rows f) (second : Compiler encodeInput rows g) :
    Compiler encodeInput rows (fun s i => f s i*g s i) := by
  let physical := halve (sub (sub (square (add first second)) (square first)) (square second))
  exact TM2ComputableInPolyTime.of_eq physical
    (fun s => List.map_congr_left (fun i _ => product_from_squares _ _))

theorem pair_from_arithmetic (a b : Nat) :
    (a+(b-a))*(a+(b-a))+a+b*(1-(b-a))=Nat.pair a b := by
  by_cases h : a < b
  · have excess : 1 ≤ b-a := by omega
    have mx : a+(b-a)=b := by omega
    simp [Nat.pair,h,mx,Nat.sub_eq_zero_of_le excess]
  · have excess : b-a=0 := by omega
    simp [Nat.pair,h,excess,Nat.add_assoc]

/-- Exact natural pairing for the time/source identifiers in finite tableaux. -/
def pair (first : Compiler encodeInput rows f) (second : Compiler encodeInput rows g) :
    Compiler encodeInput rows (fun s i => Nat.pair (f s i) (g s i)) := by
  let excess := sub second first
  let maximum := add first excess
  let physical := add (add (square maximum) first)
    (multiply second (sub (constant first 1) excess))
  exact TM2ComputableInPolyTime.of_eq physical
    (fun s => List.map_congr_left (fun i _ => pair_from_arithmetic _ _))

def signedDifference (positive : Compiler encodeInput rows f) (negative : Compiler encodeInput rows g) :
    Compiler encodeInput rows (fun s i => Encodable.encode ((f s i:Int)-g s i)) := by
  let result := add (scale (sub positive negative) 2)
    (sub (scale (sub negative positive) 2) (constant positive 1))
  exact TM2ComputableInPolyTime.of_eq result
    (fun s => List.map_congr_left (fun i _ => (UnaryColumn.encode_difference _ _).symm))

def countRows (c : Compiler encodeInput rows f) : ScalarCompiler encodeInput (fun s => (rows s).length) := by
  let result := TM2CompositionMachine.computableInPolyTime c UnaryFieldAggregate.countCompiler
  exact TM2ComputableInPolyTime.of_eq result (fun s => by simp)

def table {α : Type} (items : List α) (value : α → Nat) :
    Compiler encodeInput (fun _ : Input => items) (fun _ a => value a) :=
  TM2ConstantValueCompiler.computableInPolyTime encodeInput UnaryFieldEncoderMachine.unaryFields (items.map value)

variable [DecidableEq Index] {key value : Input → Index → Nat}
def dedupKeys (keys : Compiler encodeInput rows key) (injective : ∀ s, Function.Injective (key s)) :
    Compiler encodeInput (fun s => (rows s).dedup) key := by
  let result := UnaryFieldStableDedup.valuesComputableInPolyTime encodeInput _ keys
  exact TM2ComputableInPolyTime.of_eq result (fun s => by
    rw [UnaryFieldStableDedup.values_eq_dedup,List.dedup_map_of_injective (injective s)])

def dedup (keys : Compiler encodeInput rows key) (values : Compiler encodeInput rows value)
    (injective : ∀ s, Function.Injective (key s)) :
    Compiler encodeInput (fun s => (rows s).dedup) value := by
  classical
  let datum (s : Input) (n : Nat) : Nat := if h : ∃ i, key s i=n then value s h.choose else 0
  have atKey (s : Input) (i : Index) : datum s (key s i)=value s i := by
    simp only [datum,dif_pos (show ∃ j, key s j=key s i from ⟨i,rfl⟩)]
    congr 1
    exact injective s (Exists.choose_spec (show ∃ j, key s j=key s i from ⟨i,rfl⟩))
  let result := keyed (dedupKeys keys injective) keys values datum
    (fun s i _ => (atKey s i).symm)
    (fun _ i hi => ⟨i,List.mem_dedup.mp hi,rfl⟩)
  exact TM2ComputableInPolyTime.of_eq result (fun s => List.map_congr_left (fun i _ => atKey s i))


end LeanTrominoes.EncodedUnaryColumn
