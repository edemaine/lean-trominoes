/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnSignedEncoding

/-! # Variable-divisor unary quotient compilation -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {f : List Symbol → Index → Nat}
  {modulus bound : List Symbol → Nat}

/-- Enumerating quotient/remainder candidates gives a polynomial-time machine
when the query bound and modulus are both supplied in unary. -/
def boundedDiv (queries : Compiler rows f) (cm : ScalarCompiler modulus) (cb : ScalarCompiler bound)
    (positive : ∀ s, 0 < modulus s) (bounded : ∀ s i, i ∈ rows s → f s i < bound s) :
    Compiler rows (fun s i => f s i / modulus s) := by
  let quotients := naturalRange cb
  let remainders := naturalRange cm
  let left := cartesianLeft quotients remainders
  let right := cartesianRight quotients remainders
  let keys := add (multiplyScalar left cm) right
  apply keyed queries keys left (fun s n => n/modulus s)
  · intro s pair member
    obtain ⟨q,hq,member⟩ := List.mem_flatMap.mp member
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
    have hr := List.mem_range.mp hr
    dsimp
    simp [Nat.add_div, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr, positive s, hr]
  · intro s i hi
    let q := f s i / modulus s
    let r := f s i % modulus s
    refine ⟨(q,r),List.mem_flatMap.mpr ⟨q,List.mem_range.mpr ?_,
      List.mem_map.mpr ⟨r,List.mem_range.mpr (Nat.mod_lt _ (positive s)),rfl⟩⟩,?_⟩
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) (bounded s i hi)
    · dsimp [q,r]
      simpa [Nat.mul_comm] using Nat.div_add_mod (f s i) (modulus s)

/-- A unary column supplies its own polynomial bound: one plus its sum. -/
def columnBound (queries : Compiler rows f) :
    ScalarCompiler (fun s => ((rows s).map (f s)).sum + 1) := by
  let total : ScalarCompiler (fun s => ((rows s).map (f s)).sum) :=
    TM2CompositionMachine.computableInPolyTime queries UnaryFieldAggregate.sumCompiler
  let column : Compiler (fun _ : List Symbol => [()])
      (fun s _ => ((rows s).map (f s)).sum) := total
  exact add column (constant column 1)

/-- Variable-divisor quotient compilation needs no external magnitude bound. -/
def divide (queries : Compiler rows f) (cm : ScalarCompiler modulus)
    (positive : ∀ s, 0 < modulus s) :
    Compiler rows (fun s i => f s i / modulus s) :=
  boundedDiv queries cm (columnBound queries) positive (fun s i hi => by
    have le := List.le_sum_of_mem (List.mem_map.mpr ⟨i, hi, rfl⟩ :
      f s i ∈ (rows s).map (f s))
    omega)

end LeanTrominoes.UnaryColumn
