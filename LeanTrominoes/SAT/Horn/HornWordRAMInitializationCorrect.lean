/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMStackInvariant

/-! # Executed and semantically correct Horn initialization

This theorem stops immediately before propagation. It proves both the actual
instruction bound and the worklist representation established by that prefix.
-/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

theorem initialStack_size : initialStack.size=17 := rfl

theorem initialization_exec {w : ℕ} (input : Input)
    (width : 27*Nat.log2 (size input+2)+2≤w) :
    ∃ cost, RunsTo w bytecode (initial (encode input)) ((stackedInput input).word.at 112) cost ∧
      cost≤74*size input := by
  have log : 1≤Nat.log2 (size input+2) := by
    have mono := Nat.log_mono_right (b := 2) (show 2≤size input+2 by omega)
    simpa [← Nat.log2_eq_log_two] using mono
  have seven : 7≤w := by omega
  have capacity : 112<2^w := by
    have power : (2 : ℕ)^7≤2^w := pow_le_pow_right₀ (by decide) seven
    norm_num at power
    omega
  have whole : Contains bytecode 0 (program.assemble 0) :=
    Contains.append (program.assemble 0) [.halt Reg.output]
  change Contains bytecode 0
    (prepare.assemble 0 ++ (.seq buildIndex (.seq initialStack (.seq propagate answer)) : Code).assemble
      (0+prepare.size)) at whole
  have indexed := whole.append_right
  simp only [Structured.Code.assemble_length,Nat.zero_add] at indexed
  change Contains bytecode prepare.size
    (buildIndex.assemble prepare.size ++ (.seq initialStack (.seq propagate answer) : Code).assemble
      (prepare.size+buildIndex.size)) at indexed
  have rest := indexed.append_right
  simp only [Structured.Code.assemble_length,prepare_size,buildIndex_size,Nat.reduceAdd] at rest
  change Contains bytecode 95
    (initialStack.assemble 95 ++ (.seq propagate answer : Code).assemble (95+initialStack.size)) at rest
  have code := rest.append_left
  have stacked := (initialStack_on_input input width).compiles code
    (by rw [initialStack_size]; omega)
  have step : RunsTo w bytecode ((indexedInput input).word.at 95)
      ((stackedInput input).word.at 112) (initialStackCost (indexedInput input)) := by
    simpa only [initialStack_size,Nat.reduceAdd] using stacked
  have run := (indexed_prefix_exec input width).trans step
  refine ⟨_,run,?_⟩
  have scan := initialStackCost_le (indexedInput input)
  rw [(indexedInput_scalars input).1] at scan
  dsimp [size]
  omega

/-- Initialization establishes the complete linked index and stores exactly
the initial ready heads, with the stack pointer equal to their count. -/
theorem initialization_correct (input : Input) :
    ∃ baseline contents,
      IndexTables input (Indexed.edges input.2).length baseline ∧
      ScanRep input baseline input.2.rules.size (stackedInput input) contents ∧
      (scanEntries input baseline input.2.rules.size).reverse=
        (Worklist.stackInitial (Indexed.edges input.2).reverse (Indexed.head input.2)).queue := by
  obtain ⟨baseline,realizes,pointers,tables⟩ := indexedInput_invariant input
  obtain ⟨contents,scan⟩ := scan_invariant input baseline realizes pointers tables input.2.rules.size (by omega)
  refine ⟨baseline,contents,tables,?_,scanEntries_complete input baseline tables⟩
  simpa only [stackedInput,stackedState,(indexedInput_scalars input).1] using scan

end LeanTrominoes.Horn.WordRAM
