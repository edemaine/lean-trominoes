/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalSemantics

/-! # Actual counted loops and fixed instruction sequences for graph generation -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
variable {r w : ℕ}

def Controls (index limit : Fin r) (data : NaturalData r) (i n : ℕ) : Prop :=
  data.1 index=i ∧ data.1 limit=n

/-- A dynamic bounded loop executes the displayed body once per index.
Every test and backward jump contributes to the bound. -/
theorem loop_exec (index limit : Fin r) (body : Structured.Code r) (n budget : ℕ)
    (Invariant : ℕ → NaturalData r → Prop)
    (step : ∀ i, i < n → ∀ data, Controls index limit data i n → Invariant i data →
      ∃ result cost, NaturalData.Exec w body data result cost ∧ cost ≤ budget ∧
        Controls index limit result (i+1) n ∧ Invariant (i+1) result) :
    ∀ remaining start, start+remaining=n → ∀ data,
      Controls index limit data start n → Invariant start data →
      ∃ result cost, NaturalData.Exec w (.loop (.lt index limit) body) data result cost ∧
        cost ≤ (budget+2)*remaining+2 ∧ Controls index limit result n n ∧ Invariant n result := by
  intro remaining
  induction remaining with
  | zero =>
    intro start equal data controls invariant
    have same : start=n := by omega
    subst start
    refine ⟨data,2,?_,by omega,controls,invariant⟩
    apply Structured.Exec.loop_done
    simp only [Structured.Condition.Holds,NaturalData.word,controls.1,controls.2]
    omega
  | succ remaining ih =>
    intro start equal data controls invariant
    obtain ⟨middle,first,firstRun,firstCost,middleControls,middleInvariant⟩ :=
      step start (by omega) data controls invariant
    obtain ⟨result,later,laterRun,laterCost,resultControls,resultInvariant⟩ :=
      ih (start+1) (by omega) middle middleControls middleInvariant
    have more : (Structured.Condition.lt index limit).Holds data.word := by
      simp only [Structured.Condition.Holds,NaturalData.word,controls.1,controls.2]
      exact_mod_cast (show start < n by omega)
    refine ⟨result,first+later+2,Structured.Exec.loop_more more firstRun laterRun,?_,resultControls,resultInvariant⟩
    rw [Nat.mul_succ]
    omega

def sequence {α : Type} (one : Fin r) (code : α → Structured.Code r) : List α → Structured.Code r
  | [] => .atom (.copy one one)
  | item::rest => .seq (code item) (sequence one code rest)

/-- A fixed list of program fragments is unrolled into the actual code. The
invariant records precisely the prefix already executed. -/
theorem sequence_exec {α : Type} (one : Fin r) (code : α → Structured.Code r) (all : List α)
    (budget : ℕ) (Invariant : List α → NaturalData r → Prop) (unitWord : Fits w 1)
    (unit : ∀ done data, Invariant done data → data.1 one=1)
    (step : ∀ done item rest, done++item::rest=all → ∀ data, Invariant done data →
      ∃ result cost, NaturalData.Exec w (code item) data result cost ∧ cost ≤ budget ∧
        Invariant (done++[item]) result) :
    ∀ remaining done, done++remaining=all → ∀ data, Invariant done data →
      ∃ result cost, NaturalData.Exec w (sequence one code remaining) data result cost ∧
        cost ≤ budget*remaining.length+1 ∧ Invariant all result := by
  intro remaining
  induction remaining with
  | nil =>
    intro done complete data invariant
    have finished : done=all := by simpa only [List.append_nil] using complete
    have oneFits : Fits w (data.1 one : ℕ) := by rw [unit done data invariant]; exact unitWord
    have same : data.set one (data.1 one)=data := by apply Prod.ext; exact Function.update_eq_self _ _; rfl
    refine ⟨data,1,?_,by simp,?_⟩
    · simpa only [sequence,same] using NaturalData.copy_exec data one one oneFits
    · simpa only [finished] using invariant
  | cons item remaining ih =>
    intro done complete data invariant
    obtain ⟨middle,first,firstRun,firstCost,middleInvariant⟩ := step done item remaining complete data invariant
    have next : (done++[item])++remaining=all := by simpa only [List.append_assoc,List.cons_append,List.nil_append] using complete
    obtain ⟨result,later,laterRun,laterCost,resultInvariant⟩ := ih (done++[item]) next middle middleInvariant
    refine ⟨result,first+later,firstRun.seq laterRun,?_,resultInvariant⟩
    simp only [List.length_cons,Nat.mul_succ]
    omega

end LeanTrominoes.Domino.WordRAM.Driver
