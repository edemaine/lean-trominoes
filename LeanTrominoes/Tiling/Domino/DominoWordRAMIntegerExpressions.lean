/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitExpressionCorrectness

/-! # Integer meaning of executed binary arithmetic expressions

The interpreted integer is a mathematical invariant of digit arrays. The RAM
still stores and operates only on bounded digit, pointer, and counter words.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

def integerValues {arity length : ℕ} (inputs : Fin arity → ℤ) (slot : ℕ) : ZMod (2^length) :=
  if within : slot< arity then (inputs ⟨slot,within⟩ : ZMod (2^length)) else 0

theorem residue_of_zmod {length value : ℕ} {integer : ℤ} (bounded : value<2^length)
    (same : (value : ZMod (2^length))=(integer : ZMod (2^length))) :
    (value : ℤ)=integer%(2^length : ℕ) := by
  haveI : NeZero (2^length : ℕ) := ⟨Nat.ne_of_gt (Nat.two_pow_pos _)⟩
  have equal := congrArg (fun a : ZMod (2^length) => (a.val : ℤ)) same
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt bounded,ZMod.val_intCast] using equal

/-- A single fixed program evaluates the integer expression modulo binary
precision, with every actual instruction and every word bound certified. -/
theorem Expression.integer_program_exec {arity w base length : ℕ} (e : Expression arity)
    (data : Data) (inputs : Fin arity → ℤ)
    (known : Represents base length arity (integerValues inputs) data) (positive : 0< length)
    (zero : ∀ slot, arity≤slot → slot< arity+(e.compile arity).nodes.length →
      ∀ i< length, data.2 (slotBase base length slot+i)=0)
    (fits : Fits w (resourceBound base length (arity+(e.compile arity).nodes.length))) :
    ∃ result cost,
      NaturalData.Exec w (program (e.compile arity).nodes arity) data result cost ∧
      cost≤(26*length^2+26*length+16)*(e.compile arity).nodes.length+1 ∧
      Represents base length (arity+(e.compile arity).nodes.length)
        (evaluate (e.compile arity).nodes arity (integerValues inputs)) result ∧
      (Binary.value result.2 (slotBase base length (e.compile arity).output) length : ℤ)=
        e.eval inputs%(2^length : ℕ) ∧
      ∀ address, (address< slotBase base length arity ∨
        slotBase base length (arity+(e.compile arity).nodes.length)≤address) → result.2 address=data.2 address := by
  obtain ⟨result,cost,run,bound,correct,value,frame⟩ := e.program_exec data (integerValues inputs) known positive zero fits
  refine ⟨result,cost,run,bound,correct,?_,frame⟩
  have semantic : e.eval (fun index => integerValues (length:=length) inputs index.val)=
      ((e.eval inputs : ℤ) : ZMod (2^length)) := by
    simpa [integerValues] using e.eval_map (Int.castRingHom (ZMod (2^length))) inputs
  apply residue_of_zmod
  · exact value_lt_pow _ _ _ (correct.bits _ (e.output_lt arity (le_refl _)))
  · exact value.trans semantic

end LeanTrominoes.Domino.WordRAM.Binary.Circuit
