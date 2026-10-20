/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRemainderBody

/-! # Full arbitrary-precision remainder in bounded-word RAM

The program is fixed. Its instruction count is polynomial in the operand bit
lengths, while every arithmetic datum fits one digit word. Multiword operand
values are interpreted only in the proof, never by a primitive instruction.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Remainder
open ComplexityAbstract.RAM

/-- Every iteration consumes exactly one numerator digit. The proved bound
includes all actual loop guards and back jumps. -/
theorem loop_exec {w : ℕ} (g : Geometry) (source : ℕ → ℕ) (input : Input g source)
    (width : Widths g w) (remaining : ℕ) :
    ∀ data, remaining≤g.count → Controls g remaining data → MemoryRepresents g source remaining data →
    ∃ result cost, NaturalData.Exec w loop data result cost ∧ cost≤(29*g.precision+30)*remaining+2 ∧
      Controls g 0 result ∧ MemoryRepresents g source 0 result := by
  induction remaining with
  | zero =>
    intro data within controls memory
    refine ⟨data,2,?_,by omega,controls,memory⟩
    apply Structured.Exec.loop_done
    simp [Structured.Condition.Holds,NaturalData.word,controls.zero,controls.position]
  | succ remaining ih =>
    intro data within controls memory
    obtain ⟨middle,bodyCost,bodyRun,bodyBound,middleControls,middleMemory⟩ :=
      body_exec g source remaining data input width (by omega) controls memory
    obtain ⟨result,restCost,restRun,restBound,resultControls,resultMemory⟩ :=
      ih middle (by omega) middleControls middleMemory
    refine ⟨result,bodyCost+restCost+2,?_,?_,resultControls,resultMemory⟩
    · apply Structured.Exec.loop_more
      · simp [Structured.Condition.Holds,NaturalData.word,controls.zero,controls.position]
      · exact bodyRun
      · exact restRun
    · nlinarith only [bodyBound,restBound]

def initialized (data : WideData) : WideData :=
  ((data.set R.position (data.1 R.count)).set R.zero 0).set R.one 1

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

attribute [local simp] R.numerator R.denominator R.remainder R.difference R.precision
  R.count R.position R.address R.bit R.zero R.one NaturalData.set

theorem initialize_exec {w : ℕ} (data : WideData)
    (countFits : Fits w (data.1 R.count)) (small : Fits w (1:ℕ)) :
    NaturalData.Exec w initCode data (initialized data) 3 := by
  have h1 := NaturalData.copy_exec data R.position R.count countFits
  have h2 := NaturalData.constant_exec (data.set R.position (data.1 R.count)) R.zero 0 (fits_le small (by omega : 0≤1))
  have h3 := NaturalData.constant_exec ((data.set R.position (data.1 R.count)).set R.zero 0) R.one 1 small
  exact h1.seq (h2.seq h3)

theorem initialized_controls {g : Geometry} {data : WideData} (h : Controls g g.count data) :
    Controls g g.count (initialized data) := by
  constructor <;> simp_all [initialized,h.numerator,h.denominator,h.remainder,h.difference,h.precision,h.count]

theorem initial_memory (g : Geometry) (data : WideData)
    (zero : ∀ j< g.precision, data.2 (g.remainder+j)=0) :
    MemoryRepresents g data.2 g.count data := by
  have zeroValue : value data.2 g.remainder g.precision=0 := by
    unfold value
    apply Finset.sum_eq_zero
    intro j hj
    rw [zero j (Finset.mem_range.mp hj),zero_mul]
  constructor
  · intro j hj; rfl
  · intro j hj; rfl
  · intro j hj; rw [zero j hj]; omega
  · simp [zeroValue]
  · intro address outsideR outsideD; rfl

/-- Full binary long remainder. The numerator may use K bits, the denominator
L bits, and neither integer need fit a machine word. Precision L reserves one
guard bit above the denominator. Both operand arrays and external memory are
preserved. The result block starts as zero and is the sole remainder output. -/
theorem program_exec {w : ℕ} (g : Geometry) (data : WideData)
    (input : Input g data.2) (width : Widths g w) (controls : Controls g g.count data)
    (zero : ∀ j< g.precision, data.2 (g.remainder+j)=0) :
    ∃ result cost, NaturalData.Exec w program data result cost ∧ cost≤(29*g.precision+30)*g.count+5 ∧
      Controls g 0 result ∧ MemoryRepresents g data.2 0 result ∧
      value result.2 g.remainder g.precision=value data.2 g.numerator g.count%value data.2 g.denominator g.precision := by
  have initializedControls := initialized_controls controls
  have initializedMemory := (initial_memory g data zero).of_memory (after := initialized data) rfl
  obtain ⟨result,loopCost,run,bound,resultControls,resultMemory⟩ :=
    loop_exec g data.2 input width g.count (initialized data) (le_refl _) initializedControls initializedMemory
  refine ⟨result,3+loopCost,(initialize_exec data (by rw [controls.count]; exact width.count) width.one).seq run,
    by omega,resultControls,resultMemory,?_⟩
  simpa using resultMemory.result

theorem program_size : program.size<128 := by decide

end LeanTrominoes.Domino.WordRAM.Binary.Remainder
