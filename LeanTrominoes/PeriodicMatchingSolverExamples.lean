/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicMatchingSolver

/-! # Kernel-checked matching solver regressions -/
namespace LeanTrominoes.PeriodicBipartite
open BipartiteMatching

def chain : List (Edge (Fin 2) (Fin 2) 3) :=
  [⟨0,0,fun _ => 1000⟩,⟨0,1,fun _ => -37⟩,⟨1,0,fun _ => 29⟩]

/-- The first greedy phase must be undone by an alternating path of length two. -/
example : (compute (List.finRange 2) (buckets chain)).trace=[(2,1),(1,2)] := by decide +kernel
example : (matchingSolver chain).table.isSome=true := by decide +kernel
example : ((matchingSolver chain).table.bind (fun table => table 0)).map Edge.right=some 1 := by decide +kernel
example : ((matchingSolver chain).table.bind (fun table => table 1)).map Edge.right=some 0 := by decide +kernel
example : ((matchingSolver chain).table.bind (fun table => table 0)).map (fun e => e.offset 2)=some (-37) := by decide +kernel

def hallFailure : List (Edge (Fin 3) (Fin 3) 2) :=
  [⟨0,0,0⟩,⟨1,0,0⟩,⟨2,0,0⟩]
example : (matchingSolver hallFailure).table.isSome=false := by decide +kernel
example : (compute (List.finRange 3) (buckets hallFailure)).trace=[(3,1)] := by decide +kernel

/-- These reject before allocating or scanning the vertex arrays. -/
example : (matchingSolver ([] : List (Edge (Fin 1000000) (Fin 1000000) 17))).table.isSome=false := by decide +kernel
example : (matchingSolver ([] : List (Edge (Fin 1) (Fin 2) 0))).table.isSome=false := by decide +kernel
example : (matchingSolver ([] : List (Edge (Fin 0) (Fin 0) 0))).table.isSome=true := by decide +kernel

def parallel : List (Edge (Fin 1) (Fin 1) 3) := [⟨0,0,fun _ => 500⟩,⟨0,0,fun _ => -600⟩]
example : ((matchingSolver parallel).table.bind (fun table => table 0)).map (fun e => e.offset 1)=some 500 := by decide +kernel
example : HasPerfectMatching chain := (matchingSolver_iff chain).mp (by decide +kernel)
example : ¬ HasPerfectMatching hallFailure := by
  intro perfect
  have yes := (matchingSolver_iff hallFailure).mpr perfect
  have no : (matchingSolver hallFailure).table.isSome=false := by decide +kernel
  rw [no] at yes
  cases yes

end LeanTrominoes.PeriodicBipartite
