/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMInputBounds

/-! # Raw binary tables at the public RAM input boundary -/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM
variable {n d : ℕ}

def naturalWords (B : BasisData n d) : List ℕ :=
  [n,entryBits B,precision B] ++ (fields B).flatMap (Binary.integerDigits (precision B))

theorem words_eq_map (B : BasisData n d) : words B=(naturalWords B).map Int.ofNat := by
  simp [words,naturalWords,List.map_flatMap]

def inputMemory (B : BasisData n d) (address : ℕ) : ℕ :=
  if address=0 then (naturalWords B).length else (naturalWords B)[address-1]?.getD 0

def initialData (r : ℕ) (B : BasisData n d) : NaturalData r := (fun _ => 0,inputMemory B)

theorem initialData_word (r : ℕ) (B : BasisData n d) :
    (initialData r B).word=(initial (r:=r) (words B)).data := by
  apply Prod.ext
  · rfl
  · funext address
    by_cases zero : address=0
    · subst address
      simp [NaturalData.word,initialData,inputMemory,initial,State.data,words_eq_map]
    · cases found : (naturalWords B)[address-1]? <;>
        simp [NaturalData.word,initialData,inputMemory,initial,State.data,words_eq_map,zero,found,Int.ofNat_eq_natCast]

/-- Uniform-width field lists have the expected row-major getter. This is a
list-index identity, not any computed decoder data in the input encoding. -/
theorem flatMap_uniform_get {A C : Type*} (values : List A) (f : A → List C) (width : ℕ)
    (lengths : ∀ a∈values, (f a).length=width) (k : ℕ) (within : k< values.length)
    (j : ℕ) (digit : j< width) :
    (values.flatMap f)[k*width+j]?=(f values[k])[j]? := by
  induction values generalizing k with
  | nil => simp at within
  | cons head tail ih =>
    have headLength := lengths head List.mem_cons_self
    cases k with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by omega)]
    | succ k =>
      have indexEq : (k+1)*width+j=(f head).length+(k*width+j) := by rw [headLength]; ring
      rw [List.flatMap_cons,indexEq,List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      have tailLengths : ∀ a∈tail, (f a).length=width := fun a ha => lengths a (List.mem_cons_of_mem _ ha)
      simpa using ih tailLengths k (by simp_all)

theorem inputMemory_field (B : BasisData n d) (k : ℕ) (within : k< (fields B).length)
    (j : ℕ) (digit : j< precision B) :
    inputMemory B (4+k*precision B+j)=
      Binary.digitsMemory (precision B) (Binary.unsigned (precision B) (fields B)[k]) j := by
  have read := flatMap_uniform_get (fields B) (Binary.integerDigits (precision B)) (precision B)
    (fun _ _ => Binary.digits_length _ _) k within j digit
  have address : 4+k*precision B+j≠0 := by omega
  simp only [inputMemory,address,ite_false]
  rw [show 4+k*precision B+j-1=3+(k*precision B+j) by omega]
  rw [naturalWords,List.getElem?_append_right (by simp)]
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_sub_cancel_left]
  rw [read]
  rfl

theorem inputMemory_field_value (B : BasisData n d) (k : ℕ) (within : k< (fields B).length) :
    (Binary.value (inputMemory B) (4+k*precision B) (precision B) : ℤ)=(fields B)[k]%(2^precision B : ℤ) := by
  have values : Binary.value (inputMemory B) (4+k*precision B) (precision B)=
      Binary.value (Binary.digitsMemory (precision B) (Binary.unsigned (precision B) (fields B)[k])) 0 (precision B) := by
    unfold Binary.value
    apply Finset.sum_congr rfl
    intro j hj
    rw [inputMemory_field B k within j (Finset.mem_range.mp hj),Nat.zero_add]
  rw [values,Binary.integerDigits_value]

theorem fields_basis_get (B : BasisData n d) (i j : Fin d) :
    (fields B)[i.val*d+j.val]?=some (B.basis i j) := by
  have rowLength : ∀ a∈List.finRange d, ((List.finRange d).map (fun b => B.basis a b)).length=d := by simp
  have read := flatMap_uniform_get (List.finRange d) (fun a => (List.finRange d).map (fun b => B.basis a b)) d
    rowLength i.val (by simpa using i.isLt) j.val j.isLt
  have rowWithin : j.val< ((List.finRange d).map (fun b => B.basis (List.finRange d)[i.val] b)).length := by
    simpa using j.isLt
  rw [List.getElem?_eq_getElem rowWithin] at read
  simp only [List.getElem_map,List.getElem_finRange] at read
  unfold fields
  rw [List.getElem?_append_left (by simp [List.length_flatMap]; nlinarith [i.isLt,j.isLt])]
  exact read

theorem fields_origin_get (B : BasisData n d) (v : Fin n) (i : Fin d) :
    (fields B)[d*d+v.val*d+i.val]?=some (B.origin v i) := by
  have rowLength : ∀ a∈List.finRange n, ((List.finRange d).map (fun b => B.origin a b)).length=d := by simp
  have read := flatMap_uniform_get (List.finRange n) (fun a => (List.finRange d).map (fun b => B.origin a b)) d
    rowLength v.val (by simpa using v.isLt) i.val i.isLt
  have rowWithin : i.val< ((List.finRange d).map (fun b => B.origin (List.finRange n)[v.val] b)).length := by
    simpa using i.isLt
  rw [List.getElem?_eq_getElem rowWithin] at read
  simp only [List.getElem_map,List.getElem_finRange] at read
  unfold fields
  rw [List.getElem?_append_right (by simp [List.length_flatMap]; omega)]
  have length : ((List.finRange d).flatMap fun a => (List.finRange d).map (fun b => B.basis a b)).length=d*d := by
    simp [List.length_flatMap]
  rw [length,show d*d+v.val*d+i.val-d*d=v.val*d+i.val by omega]
  exact read

theorem basis_field_within (B : BasisData n d) (i j : Fin d) : i.val*d+j.val< (fields B).length := by
  rw [fields_length]
  nlinarith [i.isLt,j.isLt,Nat.zero_le (n*d)]

theorem origin_field_within (B : BasisData n d) (v : Fin n) (i : Fin d) : d*d+v.val*d+i.val< (fields B).length := by
  rw [fields_length]
  nlinarith [v.isLt,i.isLt]

theorem inputMemory_basis_value (B : BasisData n d) (i j : Fin d) :
    (Binary.value (inputMemory B) (4+(i.val*d+j.val)*precision B) (precision B) : ℤ)=B.basis i j%(2^precision B : ℤ) := by
  have get := fields_basis_get B i j
  rw [List.getElem?_eq_getElem (basis_field_within B i j)] at get
  rw [inputMemory_field_value B _ (basis_field_within B i j),Option.some.inj get]

theorem inputMemory_origin_value (B : BasisData n d) (v : Fin n) (i : Fin d) :
    (Binary.value (inputMemory B) (4+(d*d+v.val*d+i.val)*precision B) (precision B) : ℤ)=B.origin v i%(2^precision B : ℤ) := by
  have get := fields_origin_get B v i
  rw [List.getElem?_eq_getElem (origin_field_within B v i)] at get
  rw [inputMemory_field_value B _ (origin_field_within B v i),Option.some.inj get]

theorem inputMemory_field_bits (B : BasisData n d) (k : ℕ) (within : k< (fields B).length)
    (j : ℕ) (digit : j< precision B) : inputMemory B (4+k*precision B+j)≤1 := by
  rw [inputMemory_field B k within j digit]
  exact Binary.digitsMemory_bits _ _ _

end LeanTrominoes.Domino.WordRAM
