/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteReachHornQuery
import LeanTrominoes.SAT.Horn.HornWordRAMLinearTime

/-! # A bounded-word RAM reachability query

The graph query is represented in the dense Horn input format: a source fact,
a negative target unit, and one unary implication per edge. This has constant
space overhead per edge, and contains no reachability information or occurrence
index. The result is one for non-reachability. This is the query kernel used by
finite 2SAT; constructing covers and batching queries are separate tasks.
-/
namespace LeanTrominoes.ImplicationGraph.WordRAM
open ComplexityAbstract.RAM

abbrev Input := Σ n : ℕ, List (Fin n × Fin n) × Fin n × Fin n

def hornInput (input : Input) : Horn.WordRAM.Input :=
  ⟨input.1,queryInput input.2.1 input.2.2.1 input.2.2.2⟩

def encode (input : Input) : List ℤ := Horn.WordRAM.encode (hornInput input)
def size (input : Input) : ℕ := input.1+2*input.2.1.length+4

def Nonreachable (input : Input) : Prop :=
  ¬Relation.ReflTransGen (EdgeAdj input.2.1) input.2.2.1 input.2.2.2

theorem hornInput_size (input : Input) : Horn.WordRAM.size (hornInput input)=size input := by
  have native := query_size input.2.1 input.2.2.1 input.2.2.2
  simp only [Horn.Indexed.inputSize] at native
  simp only [Horn.WordRAM.size,hornInput,Horn.Indexed.edges_length,size]
  omega

/-- The dense query encoding has seven header/fact/target words and three
words per graph edge; it contains no transitive-closure table. -/
theorem encode_length (input : Input) : (encode input).length=3*input.2.1.length+7 := by
  have rules : (hornInput input).2.rules.size=input.2.1.length+2 := by simp [hornInput,queryInput]
  have counts := hornInput_size input
  change input.1+(hornInput input).2.rules.size+(Horn.Indexed.edges (hornInput input).2).length+1=
    input.1+2*input.2.1.length+4 at counts
  rw [rules] at counts
  have occurrences : (Horn.Indexed.edges (hornInput input).2).length=input.2.1.length+1 := by omega
  simp only [encode,Horn.WordRAM.encode,List.length_map,Horn.WordRAM.words_length,rules,occurrences]
  omega

theorem hornInput_correct (input : Input) :
    Horn.Satisfiable (hornInput input).2.rules.toList ↔ Nonreachable input :=
  query_satisfiable_iff input.2.1 input.2.2.1 input.2.2.2

/-- One fixed word-RAM program answers each query in a linear number of
primitive instructions, for all sufficiently large logarithmic word sizes. -/
theorem decidesWithin :
    DecidesWithin encode Nonreachable (fun input => 120*(size input+1))
      (fun input => 27*Nat.log2 (size input+2)+2) := by
  obtain ⟨registers,program,verified⟩ := Horn.WordRAM.decidesWithin
  refine ⟨registers,program,?_⟩
  intro input w width fits
  obtain ⟨steps,value,execution,time,boolean,correct⟩ := verified (hornInput input) w
    (by simpa only [hornInput_size] using width) fits
  exact ⟨steps,value,execution,by simpa only [hornInput_size] using time,boolean,
    correct.trans (hornInput_correct input)⟩

theorem linearTime : LinearTime encode size Nonreachable := ⟨120,27,decidesWithin⟩

end LeanTrominoes.ImplicationGraph.WordRAM
