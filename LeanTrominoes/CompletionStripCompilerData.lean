/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripOccupancyExpr
import LeanTrominoes.PartrecUnpackDigitsSpace

/-! # Finite data for the uncovered-strip compiler -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
open BoundedArithmetic BoundedArithmetic.Expr
open Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

instance (t : Tromino) (input : PeriodicStripTrominoPrefill) (x y : Nat) : Decidable (Covered t input x y) := by
  unfold Covered
  infer_instance

def gridCell (input : PeriodicStripTrominoPrefill) (index : Nat) : Cell :=
  ((index / input.height : Nat),(index % input.height : Nat))

def emitted (t : Tromino) (input : PeriodicStripTrominoPrefill) (count : Nat) : List Cell :=
  ((List.range count).filter fun i => ¬ Covered t input (i/input.height) (i%input.height)).map (gridCell input)

def records (t : Tromino) (input : PeriodicStripTrominoPrefill) (count : Nat) : List Nat :=
  (emitted t input count).flatMap PeriodicStripFlatEncoding.cellFields

def base (input : PeriodicStripTrominoPrefill) : Nat := 2*(input.height+input.period+1)

def payload (t : Tromino) (input : PeriodicStripTrominoPrefill) (index : Nat) : List Nat :=
  [PackedFields.pack (base input) (records t input index).reverse,(records t input index).length,index] ++ fields input

theorem records_length (t : Tromino) (input : PeriodicStripTrominoPrefill) (n : Nat) :
    (records t input n).length = 2*(emitted t input n).length := by
  simp [records,List.length_flatMap,PeriodicStripFlatEncoding.cellFields,List.sum_replicate,Nat.mul_comm]

theorem emitted_length_le (t : Tromino) (input : PeriodicStripTrominoPrefill) (n : Nat) :
    (emitted t input n).length ≤ n := by
  simpa [emitted] using List.length_filter_le (fun i => decide (¬Covered t input (i/input.height) (i%input.height))) (List.range n)

theorem mem_emitted (t : Tromino) (input : PeriodicStripTrominoPrefill) (n : Nat) (c : Cell) :
    c ∈ emitted t input n ↔ ∃ i < n, ¬ Covered t input (i/input.height) (i%input.height) ∧ gridCell input i = c := by
  simp [emitted,and_assoc]

theorem emitted_succ (t : Tromino) (input : PeriodicStripTrominoPrefill) (n : Nat) :
    emitted t input (n+1) = emitted t input n ++
      if Covered t input (n/input.height) (n%input.height) then [] else [gridCell input n] := by
  by_cases h : Covered t input (n/input.height) (n%input.height) <;>
    simp [emitted,List.range_succ,List.filter_append,h]

theorem records_succ (t : Tromino) (input : PeriodicStripTrominoPrefill) (n : Nat) :
    records t input (n+1) = records t input n ++
      if Covered t input (n/input.height) (n%input.height) then [] else [2*(n/input.height),2*(n%input.height)] := by
  rw [records,emitted_succ,List.flatMap_append]
  have coords : PeriodicStripFlatEncoding.cellFields (gridCell input n) = [2*(n/input.height),2*(n%input.height)] := rfl
  by_cases h : Covered t input (n/input.height) (n%input.height)
  · simp [h,records]
  · simp only [if_neg h,List.flatMap_cons,List.flatMap_nil,List.append_nil,coords]
    rfl

def compiledStrip (t : Tromino) (input : PeriodicStripTrominoPrefill) : PeriodicStrip :=
  ⟨input.height,input.period,emitted t input (input.period*input.height)⟩

theorem compiled_motif (t : Tromino) (input : PeriodicStripTrominoPrefill) (hh : 0 < input.height) (c : Cell) :
    c ∈ (compiledStrip t input).motif ↔ c ∈ (uncoveredStrip t input).motif := by
  change c ∈ emitted t input (input.period*input.height) ↔ c ∈ (occupiedStrip t input).complement.motif
  rw [PeriodicStrip.mem_complement_motif,mem_emitted]
  constructor
  · rintro ⟨i,hi,absent,rfl⟩
    have ylt := Nat.mod_lt i hh
    have xlt : i / input.height < input.period := (Nat.div_lt_iff_lt_mul hh).mpr hi
    change (0 ≤ ((i/input.height : Nat) : Int) ∧ ((i/input.height : Nat) : Int) < input.period ∧
      0 ≤ ((i%input.height : Nat) : Int) ∧ ((i%input.height : Nat) : Int) < input.height) ∧ _
    refine ⟨⟨by positivity,by exact_mod_cast xlt,by positivity,by exact_mod_cast ylt⟩,?_⟩
    exact fun member => absent ((covered_iff t input _ _ ylt).mpr member)
  · rintro ⟨⟨hx,hp,hy,hh'⟩,absent⟩
    change c.1 < (input.period : Int) at hp
    change c.2 < (input.height : Int) at hh'
    let x := c.1.toNat
    let y := c.2.toNat
    have ex : (x : Int) = c.1 := Int.toNat_of_nonneg hx
    have ey : (y : Int) = c.2 := Int.toNat_of_nonneg hy
    have hxl : x < input.period := by omega
    have hyl : y < input.height := by omega
    have div : (x*input.height+y)/input.height = x := by
      rw [Nat.add_comm,Nat.mul_comm x input.height,Nat.add_mul_div_left _ _ hh,Nat.div_eq_of_lt hyl]
      omega
    have mod : (x*input.height+y)%input.height = y := by simp [Nat.add_mod,Nat.mod_eq_of_lt hyl]
    refine ⟨x*input.height+y,by nlinarith,?_,?_⟩
    · rw [div,mod]
      intro covered
      have member := (covered_iff t input x y hyl).mp covered
      apply absent
      simpa [ex,ey] using member
    · simp only [gridCell,div,mod,ex,ey,Prod.mk.eta]


theorem records_bounded (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) (n : Nat) (hn : n ≤ input.period*input.height) :
    ∀ a ∈ records t input n, a < base input := by
  intro a ha
  obtain ⟨c,hc,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨i,hi,_,rfl⟩ := (mem_emitted t input n c).mp hc
  have xlt : i/input.height < input.period :=
    (Nat.div_lt_iff_lt_mul hh).mpr (lt_of_lt_of_le hi hn)
  have ylt := Nat.mod_lt i hh
  change a ∈ [2*(i/input.height),2*(i%input.height)] at ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl <;> unfold base <;> omega

theorem compiled_carrier (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) :
    (compiledStrip t input).carrier = (uncoveredStrip t input).carrier := by
  ext c
  simp only [PeriodicStrip.mem_carrier_iff]
  change (0 ≤ c.2 ∧ c.2 < (input.height : Int) ∧ ∃ b ∈ (compiledStrip t input).motif,
    b.2 = c.2 ∧ (input.period : Int) ∣ c.1-b.1) ↔ _
  simp only [compiled_motif t input hh]
  rfl

theorem compiled_wellFormed (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) (hp : 0 < input.period) :
    (compiledStrip t input).IsWellFormed := by
  refine ⟨hh,hp,?_⟩
  intro c hc
  exact (uncoveredStrip_wellFormed t input hh hp).2.2 c
    ((compiled_motif t input hh c).mp hc)

theorem compiled_tiling_iff (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) (hp : 0 < input.period) :
    PeriodicStripTrominoTiling t (compiledStrip t input) ↔
      PeriodicStripTrominoTiling t (uncoveredStrip t input) := by
  simp only [PeriodicStripTrominoTiling,compiled_carrier t input hh,
    compiled_wellFormed t input hh hp,uncoveredStrip_wellFormed t input hh hp,true_and]

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
