/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBatch
import LeanTrominoes.SAT.Horn.HornWordRAMLinearTime

/-! # The actual RAM kernel for simultaneous opposite-reachability queries

The kernel reads the expanded dense Horn table. Constructing that table from
an original graph, and constructing a periodic cover from clauses, are separate
compilation steps. The execution theorem here does not charge them implicitly.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATBatch.WordRAM
open ComplexityAbstract.RAM

abbrev Input := Σ n : ℕ, Σ p : ℕ, List (Fin n × Fin n) × (Fin p → Fin n × Fin n)

def hornInput (a : Input) : Horn.WordRAM.Input :=
  ⟨a.2.1*2*a.1,TwoSATBatch.input a.2.2.1 a.2.2.2⟩

def encode (a : Input) : List ℤ := Horn.WordRAM.encode (hornInput a)
def size (a : Input) : ℕ := 2*a.2.1*a.1+5*a.2.1+4*a.2.1*a.2.2.1.length+1

def Consistent (a : Input) : Prop := TwoSATBatch.Consistent a.2.2.1 a.2.2.2

theorem horn_size (a : Input) : Horn.WordRAM.size (hornInput a)=size a :=
  TwoSATBatch.input_size a.2.2.1 a.2.2.2

theorem correct (a : Input) : Horn.Satisfiable (hornInput a).2.rules.toList ↔ Consistent a :=
  TwoSATBatch.input_correct a.2.2.1 a.2.2.2

theorem encode_length (a : Input) :
    (encode a).length=3+7*a.2.1+6*a.2.1*a.2.2.1.length := by
  simp only [encode,Horn.WordRAM.encode,List.length_map,Horn.WordRAM.words_length,hornInput,
    TwoSATBatch.input_rules,TwoSATBatch.input_occurrences]
  ring

/-- Exact operational certificate for one invocation of the complete Horn program. -/
theorem program_verified (a : Input) (w : ℕ)
    (width : 27*Nat.log2 (size a+2)+2≤w) :
    Horn.WordRAM.program.size<2^w ∧ ∃ result : Data 32, ∃ steps,
      Structured.Exec w Horn.WordRAM.program (initial (r := 32) (encode a)).data result steps ∧
      steps+1≤120*(size a+1) ∧ Fits w (result.1 Horn.WordRAM.Reg.output) ∧
      (result.1 Horn.WordRAM.Reg.output=0 ∨ result.1 Horn.WordRAM.Reg.output=1) ∧
      (result.1 Horn.WordRAM.Reg.output=1 ↔ Consistent a) := by
  obtain ⟨capacity,result,steps,execution,bound,fits,boolean,answer⟩ :=
    Horn.WordRAM.program_verified (hornInput a) w (by simpa only [horn_size] using width)
  exact ⟨capacity,result,steps,execution,by simpa only [horn_size] using bound,fits,boolean,
    answer.trans (correct a)⟩

theorem decidesWithin : DecidesWithin encode Consistent
    (fun a => 120*(size a+1)) (fun a => 27*Nat.log2 (size a+2)+2) := by
  obtain ⟨registers,program,verified⟩ := Horn.WordRAM.decidesWithin
  refine ⟨registers,program,?_⟩
  intro a w width fits
  obtain ⟨steps,value,execution,time,boolean,answer⟩ := verified (hornInput a) w
    (by simpa only [horn_size] using width) fits
  exact ⟨steps,value,execution,by simpa only [horn_size] using time,boolean,answer.trans (correct a)⟩

theorem linearTime : LinearTime encode size Consistent := ⟨120,27,decidesWithin⟩

end LeanTrominoes.ImplicationGraph.TwoSATBatch.WordRAM
