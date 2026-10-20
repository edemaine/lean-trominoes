/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMPackMemory

/-! # Checked vertex count and cold matching allocation budget -/
namespace LeanTrominoes.BipartiteMatching.PackWordRAM
open ComplexityAbstract.RAM ImplicationGraph.TwoSATExpression
set_option maxRecDepth 8000
set_option maxHeartbeats 1500000

def vertexCount (n d : Nat) := n*2^d+1
def coldCapacity (n edges : Nat) := 4*(2*n+edges+3)^8

def metadata (d : Nat) : List (Assignment 86) :=
  [⟨84,.arithmetic .add (.arithmetic .mul (.inputValue 66) (.constant (2^d : Nat))) (.constant 1)⟩,
   ⟨85,.arithmetic .add (.arithmetic .add (.arithmetic .mul (.constant 2) (.inputValue 84)) (.inputValue 83)) (.constant 3)⟩,
   ⟨85,.arithmetic .mul (.inputValue 85) (.inputValue 85)⟩,
   ⟨85,.arithmetic .mul (.inputValue 85) (.inputValue 85)⟩,
   ⟨85,.arithmetic .mul (.inputValue 85) (.inputValue 85)⟩,
   ⟨85,.arithmetic .mul (.constant 4) (.inputValue 85)⟩]
def metadataCode (d : Nat) : Structured.Code 128 := Assignment.sequence 42 (by decide) 85 (metadata d)

theorem metadata_exec {n d edges w : Nat} (data : Data 128)
    (nValue : data.1 66=n) (edgesValue : data.1 83=edges)
    (capFits : Fits w (coldCapacity (vertexCount n d) edges))
    (phaseFits : Fits w (2^d : Nat)) :
    ∃ result, Structured.Exec w (metadataCode d) data result 31 ∧ result.2=data.2 ∧
      result.1 84=vertexCount n d ∧ result.1 85=coldCapacity (vertexCount n d) edges ∧
      (∀ reg : Fin 128, reg.val<86 → reg≠84 → reg≠85 → result.1 reg=data.1 reg) := by
  let N := vertexCount n d
  let base := 2*N+edges+3
  let cap := coldCapacity N edges
  have basePositive : 1≤base := by dsimp [base]; omega
  have basePower : base≤base^8 := by simpa only [pow_one] using (pow_le_pow_right₀ basePositive (show 1≤8 by decide))
  have powerCap : base^8≤cap := by dsimp [cap,coldCapacity,base]; omega
  have baseCap : base≤cap := basePower.trans powerCap
  have boundN : N≤cap := by dsimp [base] at baseCap; omega
  have boundEdges : edges≤cap := by dsimp [base] at baseCap; omega
  have boundMul : n*2^d≤cap := by dsimp [N,vertexCount] at boundN; omega
  have boundNInput : n≤cap := by
    have power : 1≤(2 : Nat)^d := Nat.one_le_two_pow
    have grow := Nat.mul_le_mul_left n power
    omega
  have bound2 : base^2≤cap := (pow_le_pow_right₀ basePositive (show 2≤8 by decide)).trans powerCap
  have bound4 : base^4≤cap := (pow_le_pow_right₀ basePositive (show 4≤8 by decide)).trans powerCap
  have fits (x : Nat) (bound : x≤cap) : Fits w x := Allocation.nat_fits_le capFits bound
  have f0 := fits 0 (Nat.zero_le _)
  have f1 := fits 1 (by omega)
  have f2 := fits 2 (by dsimp [base] at baseCap; omega)
  have f3 := fits 3 (by dsimp [base] at baseCap; omega)
  have f4 := fits 4 (by dsimp [base,N,vertexCount] at baseCap; omega)
  have fn := fits n boundNInput
  have fe := fits edges boundEdges
  have fm := fits (n*2^d) boundMul
  have fN := fits N boundN
  have f2N := fits (2*N) (by dsimp [base] at baseCap; omega)
  have fmixed := fits (2*N+edges) (by dsimp [base] at baseCap; omega)
  have fb := fits base baseCap
  have fsquare := fits (base^2) bound2
  have ffour := fits (base^4) bound4
  have feight := fits (base^8) powerCap
  have fc := capFits
  have safe : Assignment.Safe w 85 (metadata d) (environment data) data.2 := by
    simp only [N,vertexCount,base,cap,coldCapacity,pow_succ,pow_zero,mul_one,one_mul,mul_assoc,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_one,Nat.cast_zero] at f0 f1 f2 f3 f4 fn fe fm fN f2N fmixed fb fsquare ffour feight fc phaseFits
    simp [metadata,Assignment.Safe,Assignment.update,Expr.Safe,Expr.eval,Arithmetic.eval,
      environment,input,nValue,edgesValue,Function.update_apply,
      f1,f2,f3,f4,fn,fe,fm,fN,f2N,fmixed,fb,fsquare,ffour,feight,fc,phaseFits,Nat.cast_add,Nat.cast_mul,mul_assoc]
  have small : ∀ a∈metadata d, a.expression.nodes≤42 := by simp [metadata,Expr.nodes]
  obtain ⟨result,run,memory,values⟩ := Assignment.sequence_exec (metadata d) (by decide) small 85
    (environment data) data (fun _ => rfl) safe
  refine ⟨result,?_,memory,?_,?_,?_⟩
  · simpa only [metadataCode,metadata,Assignment.cost,Expr.nodes,Nat.reduceAdd] using run
  · simpa [metadata,Assignment.evaluate,Assignment.update,Expr.eval,Arithmetic.eval,environment,input,
      Assignment.inputRegister,nValue,edgesValue,Function.update_apply,vertexCount,Nat.cast_add,Nat.cast_mul] using values 84
  · have value := values 85
    simp [metadata,Assignment.evaluate,Assignment.update,Expr.eval,Arithmetic.eval,environment,input,
      Assignment.inputRegister,nValue,edgesValue,Function.update_apply] at value
    rw [value]
    simp only [coldCapacity,vertexCount,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_pow]
    ring
  · intro reg small ne84 ne85
    let i : Fin 86 := ⟨reg.val,small⟩
    have eq : input i=reg := by apply Fin.ext; rfl
    have i84 : i≠84 := by
      intro same
      have equal : i.val=(84 : Fin 86).val := congrArg (fun j : Fin 86 => j.val) same
      exact ne84 (Fin.ext equal)
    have i85 : i≠85 := by
      intro same
      have equal : i.val=(85 : Fin 86).val := congrArg (fun j : Fin 86 => j.val) same
      exact ne85 (Fin.ext equal)
    have value := values i
    rw [show Assignment.inputRegister 42 i=reg from eq] at value
    simpa [metadata,Assignment.evaluate,Assignment.update,i84,i85,Function.update_of_ne,environment,eq] using value

end LeanTrominoes.BipartiteMatching.PackWordRAM
