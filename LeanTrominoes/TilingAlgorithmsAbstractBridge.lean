/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingAbstractBridge
import LeanTrominoes.Tiling.Domino.DominoWordRAMPolynomialTime
import LeanTrominoes.Computation.RAM.Recode

/-! # Original integer matrix inputs for the tiling abstract

The public representation uses only matrices, coordinate functions, and raw
binary digits. Precision padding depends on the fixed dimension, and is
chosen in the proof rather than referring to implementation constants.
-/
namespace LeanTrominoes.TilingAlgorithmsAbstractBridge

abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev BasisData (n d : ℕ) := Matrix (Fin d) (Fin d) ℤ × (Fin n → Lattice d)

def BasisData.basis {n d : ℕ} (B : BasisData n d) := B.1
def BasisData.origin {n d : ℕ} (B : BasisData n d) := B.2

def BasisData.realize {n d : ℕ} (B : BasisData n d) (a : Fin n × Lattice d) : Lattice d :=
  B.origin a.1+B.basis.mulVec a.2

def BasisData.Valid {n d : ℕ} (B : BasisData n d) : Prop :=
  B.basis.det≠0 ∧ Function.Injective B.realize

def BasisData.region {n d : ℕ} (B : BasisData n d) : Set (Lattice d) := Set.range B.realize

abbrev Input (d : ℕ) := Σ n : ℕ, {B : BasisData n d // B.Valid}

def magnitude {n d : ℕ} (B : BasisData n d) : ℕ :=
  1+(∑ i, ∑ j, (B.basis i j).natAbs)+(∑ v, ∑ i, (B.origin v i).natAbs)

def entryBits {n d : ℕ} (B : BasisData n d) : ℕ := Nat.log2 (magnitude B+1)+2

def precision {n d : ℕ} (padding : ℕ) (B : BasisData n d) : ℕ := padding*entryBits B+4

def bits (length value : ℕ) : List ℤ :=
  (List.range length).map (fun i => ((value/2^i)%2 : ℕ))

def integerBits (length : ℕ) (z : ℤ) : List ℤ := bits length (z%(2^length : ℤ)).toNat

def fields {n d : ℕ} (B : BasisData n d) : List ℤ :=
  (List.finRange d).flatMap (fun i => (List.finRange d).map (fun j => B.basis i j)) ++
    (List.finRange n).flatMap (fun v => (List.finRange d).map (fun i => B.origin v i))

def words {n d : ℕ} (padding : ℕ) (B : BasisData n d) : List ℤ :=
  [(n : ℤ),(entryBits B : ℤ),(precision padding B : ℤ)]++
    (fields B).flatMap (integerBits (precision padding B))

def encode {d : ℕ} (padding : ℕ) (input : Input d) : List ℤ := words padding input.2.val

def size {d : ℕ} (padding : ℕ) (input : Input d) : ℕ :=
  input.1+entryBits input.2.val+precision padding input.2.val+(encode padding input).length+1

def Tileable {d : ℕ} (input : Input d) : Prop :=
  ∃ chosen, TilingAbstractBridge.Data.DominoTiling input.2.val.region chosen

def dataEquiv (n d : ℕ) : BasisData n d ≃ Domino.BasisData n d where
  toFun B := ⟨B.origin,B.basis⟩
  invFun B := (B.basis,B.origin)
  left_inv _ := rfl
  right_inv B := by cases B; rfl

theorem valid_iff {n d : ℕ} (B : BasisData n d) : B.Valid ↔ (dataEquiv n d B).Valid := Iff.rfl

theorem region_eq {n d : ℕ} (B : BasisData n d) (valid : B.Valid) :
    B.region=((dataEquiv n d B).chart valid).region := by
  ext x
  rfl

abbrev NativeInput (d : ℕ) := Σ n : ℕ, {B : Domino.BasisData n d // B.Valid}

def inputEquiv (d : ℕ) : Input d ≃ NativeInput d where
  toFun input := ⟨input.1,⟨dataEquiv _ _ input.2.val,input.2.property⟩⟩
  invFun input := ⟨input.1,⟨(dataEquiv _ _).symm input.2.val,input.2.property⟩⟩
  left_inv _ := rfl
  right_inv input := by rcases input with ⟨n,B,valid⟩; cases B; rfl

def nativePadding (d : ℕ) := Domino.decoderWordFactor d+Domino.WordRAM.determinantWordFactor d

theorem precision_eq {n d : ℕ} (B : BasisData n d) :
    precision (nativePadding d) B=Domino.WordRAM.precision (dataEquiv n d B) := rfl

theorem bits_eq_native (length value : ℕ) :
    bits length value=(Domino.WordRAM.Binary.digits length value).map Int.ofNat := by
  induction length generalizing value with
  | zero => rfl
  | succ length ih =>
    rw [Domino.WordRAM.Binary.digits,List.map_cons,←ih]
    simp [bits,List.range_succ_eq_map,List.map_map,Function.comp_def,pow_succ',Nat.div_div_eq_div_mul]

theorem words_eq_native {n d : ℕ} (B : BasisData n d) :
    words (nativePadding d) B=Domino.WordRAM.words (dataEquiv n d B) := by
  unfold words Domino.WordRAM.words
  rw [precision_eq]
  congr 1
  apply List.flatMap_congr
  intro z hz
  exact bits_eq_native _ _

theorem size_eq_native {d : ℕ} (input : Input d) :
    size (nativePadding d) input=Domino.WordRAM.size (dataEquiv _ _ input.2.val) := by
  simp only [size,encode,words_eq_native,precision_eq]
  rfl

theorem predicate_iff {d : ℕ} (input : Input d) :
    Tileable input ↔ Domino.WordRAM.predicate (inputEquiv d input) := by
  change (∃ chosen, TilingAbstractBridge.Data.DominoTiling input.2.val.region chosen) ↔
    Domino.Tileable ((dataEquiv _ _ input.2.val).chart input.2.property).region
  rw [region_eq input.2.val input.2.property]
  apply exists_congr
  intro chosen
  exact TilingAbstractBridge.Native.domino_tiling_iff _ _

theorem polynomialTime (d : ℕ) : ∃ padding,
    ComplexityAbstract.RAM.PolynomialTime (encode (d:=d) padding) (size padding) Tileable := by
  refine ⟨nativePadding d,?_⟩
  exact ComplexityAbstract.RAM.PolynomialTime.recode
    (nativeEncode:=Domino.WordRAM.encode) (nativeSize:=Domino.WordRAM.inputSize)
    (q:=Domino.WordRAM.predicate) (inputEquiv d)
    (fun input => words_eq_native input.2.val) size_eq_native predicate_iff
    (Domino.WordRAM.polynomialTime d)

end LeanTrominoes.TilingAlgorithmsAbstractBridge
