/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBatchWordRAM
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATWordBounds

/-! # One Horn batch for the complete periodic 2SAT criterion

This module proves the semantic compilation and its size bound. The cover and
Horn tables here are mathematical values. Their actual construction from the
original clause encoding requires the separate table-generation RAM program.
-/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open ComplexityAbstract.RAM
open ImplicationGraph

variable {n d : ℕ}

def pairs (n d : ℕ) : Fin n → Fin (n*2*(period (Fin n) d)^d) × Fin (n*2*(period (Fin n) d)^d) :=
  fun a => (coverIndex n d (period (Fin n) d) ((a,true),0),
    coverIndex n d (period (Fin n) d) ((a,false),0))

def coverInput (formula : Formula (Fin n) d) : TwoSATBatch.WordRAM.Input :=
  ⟨n*2*(period (Fin n) d)^d,n,coverEdges formula (period (Fin n) d),pairs n d⟩

theorem consistent_iff_cover (formula : Formula (Fin n) d) :
    TwoSATBatch.WordRAM.Consistent (coverInput formula) ↔ ∀ a : Fin n,
      ¬(PeriodicLatticeGraph.CoverReach (arcs formula) (period (Fin n) d) ((a,true),0) ((a,false),0) ∧
        PeriodicLatticeGraph.CoverReach (arcs formula) (period (Fin n) d) ((a,false),0) ((a,true),0)) := by
  simp only [TwoSATBatch.WordRAM.Consistent,TwoSATBatch.Consistent,coverInput,pairs]
  simp only [coverEdges_reach]

def rejectInput : Horn.WordRAM.Input := ⟨0,⟨#[⟨[],none⟩]⟩⟩

def compiledInput (formula : Formula (Fin n) d) : Horn.WordRAM.Input :=
  if none ∈ formula then rejectInput else TwoSATBatch.WordRAM.hornInput (coverInput formula)

theorem compiled_correct (formula : Formula (Fin n) d) (locality : Local formula) :
    Horn.Satisfiable (compiledInput formula).2.rules.toList ↔ Satisfiable formula := by
  by_cases empty : none ∈ formula
  · have eq : compiledInput formula=rejectInput := by simp [compiledInput,empty]
    rw [eq,satisfiable_iff_cover formula locality]
    simp only [empty,not_true_eq_false,false_and,iff_false]
    rintro ⟨model,satisfied⟩
    exact satisfied ⟨[],none⟩ (by simp [rejectInput]) (by simp)
  · have eq : compiledInput formula=TwoSATBatch.WordRAM.hornInput (coverInput formula) := by
      simp [compiledInput,empty]
    rw [eq,satisfiable_iff_cover formula locality]
    simp only [empty,not_false_eq_true,true_and]
    exact (TwoSATBatch.WordRAM.correct (coverInput formula)).trans (consistent_iff_cover formula)

theorem compiled_size (formula : Formula (Fin n) d) :
    Horn.WordRAM.size (compiledInput formula)≤18*(sizeBound formula+1)^3 := by
  unfold compiledInput
  split_ifs
  · simp only [rejectInput,Horn.WordRAM.size,Horn.Indexed.edges]
    norm_num
    have h : 0<(sizeBound formula+1)^3 := pow_pos (by omega) _
    omega
  · rw [TwoSATBatch.WordRAM.horn_size]
    simp only [TwoSATBatch.WordRAM.size,coverInput]
    have nbound : n≤sizeBound formula := by unfold sizeBound; omega
    obtain ⟨_,_,vertices,edges⟩ := cover_magnitudes formula
    have a := Nat.mul_le_mul nbound vertices
    have b := Nat.mul_le_mul nbound edges
    nlinarith [sq_nonneg (sizeBound formula : ℤ)]

end LeanTrominoes.PeriodicTwoSAT.WordRAM
