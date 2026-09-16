/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TM2ComputableInPolyTimeCongr
import LeanTrominoes.UnaryFieldResidueCompiler
import LeanTrominoes.UnaryPointTableCompiler
import LeanTrominoes.UnaryAlignedDifferenceCompiler
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Compositional polynomial-time arithmetic on indexed unary columns -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]

abbrev Compiler (rows : List Symbol → List Index) (value : List Symbol → Index → Nat) :=
  TM2ComputableInPolyTime id unaryFields (fun s => (rows s).map (value s))

variable {rows : List Symbol → List Index} {f g : List Symbol → Index → Nat}

def residue (c : Compiler rows f) (m : Nat) (positive : 0 < m) (table : Fin m → Nat) :
    Compiler rows (fun s i => table ⟨f s i % m,Nat.mod_lt _ positive⟩) := by
  let result := TM2CompositionMachine.computableInPolyTime c
    (UnaryFieldResidue.computableInPolyTime m positive table)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by simp [List.map_map]))

def constant (c : Compiler rows f) (n : Nat) : Compiler rows (fun _ _ => n) := by
  exact residue c 1 (by decide) (fun _ => n)

def scale (c : Compiler rows f) (n : Nat) : Compiler rows (fun s i => f s i*n) := by
  let result := TM2CompositionMachine.computableInPolyTime c (UnaryFieldConstantScale.computableInPolyTime n)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by simp [UnaryFieldConstantScale.values,List.map_map]))

def halve (c : Compiler rows f) : Compiler rows (fun s i => f s i/2) := by
  let result := TM2CompositionMachine.computableInPolyTime c UnaryFieldHalve.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by simp [List.map_map]))

def divPowTwo (c : Compiler rows f) : (k : Nat) → Compiler rows (fun s i => f s i/2^k)
  | 0 => TM2ComputableInPolyTime.of_eq c (by intro s; simp)
  | k+1 => TM2ComputableInPolyTime.of_eq (halve (divPowTwo c k)) (by
      intro s
      simp [List.map_map,Nat.div_div_eq_div_mul,Nat.pow_succ])

def add (a : Compiler rows f) (b : Compiler rows g) : Compiler rows (fun s i => f s i+g s i) := by
  let result := AlignedUnaryListClosure.addedComputableInPolyTime id _ _ (fun s => by simp) a b
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (UnaryAlignedAddMachine.sums_map _ _ _))

def sub (a : Compiler rows f) (b : Compiler rows g) : Compiler rows (fun s i => f s i-g s i) := by
  let result := UnaryAlignedDifference.nativeListComputableInPolyTime true _ _ (fun s => by simp) a b
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [UnaryAlignedDifference.values_eq_zipWith]
  simp only [↓reduceIte,List.zipWith_map]
  induction rows s with
  | nil => rfl
  | cons i rest ih => simp [ih]

def lookup (c : Compiler rows f) (table : List Nat)
    (bounded : ∀ s i, i ∈ rows s → f s i < table.length) :
    Compiler rows (fun s i => table[f s i]?.getD 0) := by
  let result := UnaryIndexedValueLookup.valuesComputableInPolyTime id _ (fun _ => table) c
    (TM2ConstantValueCompiler.computableInPolyTime id unaryFields table)
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  congr 1
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    exact bounded s i hi)]
  simp [List.map_map]

def cartesianLeft {Other : Type} {other : List Symbol → List Other}
    {value : List Symbol → Other → Nat} (a : Compiler rows f) (b : Compiler other value) :
    Compiler (fun s => (rows s).flatMap fun i => (other s).map fun j => (i,j))
      (fun s p => f s p.1) := by
  let result := UnaryFieldCartesian.computableInPolyTime id _ _ a b .first
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by
      simp [UnaryFieldSquareProjection.choose,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]))

def cartesianRight {Other : Type} {other : List Symbol → List Other}
    {value : List Symbol → Other → Nat} (a : Compiler rows f) (b : Compiler other value) :
    Compiler (fun s => (rows s).flatMap fun i => (other s).map fun j => (i,j))
      (fun s p => value s p.2) := by
  let result := UnaryFieldCartesian.computableInPolyTime id _ _ a b .second
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
    (fun s => congrArg unaryFields (by
      simp [UnaryFieldSquareProjection.choose,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]))
end LeanTrominoes.UnaryColumn
