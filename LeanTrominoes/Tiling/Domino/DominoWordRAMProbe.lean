/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMNumerator
import LeanTrominoes.Tiling.Domino.DominoWordRAMDecoderRawExpressions

/-! # Executing an integer circuit and testing its signed result -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Probe
open ComplexityAbstract.RAM
abbrev Data := NaturalData 64
abbrev Code := Structured.Code 64

noncomputable def program {arity : ℕ} (e : Circuit.Expression arity) : Code :=
  .seq ((Circuit.program (e.compile arity).nodes arity).embed 47) Numerator.program

theorem extend_high (data : Data) (result : Circuit.Data) (i : Fin 64) (high : 17≤ i.val) :
    (result.extend (NaturalData.upper (r:=17) (s:=47) data)).1 i=data.1 i := by
  let j : Fin 47 := ⟨i.val-17,by have := i.isLt; omega⟩
  have same : j.natAdd 17=i := by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    dsimp only [j]
    omega
  rw [←same,NaturalData.extend_right]
  rfl

theorem controls_extend {g : Numerator.Geometry} {data : Data}
    (h : Numerator.Controls g data) (result : Circuit.Data) :
    Numerator.Controls g (result.extend (NaturalData.upper (r:=17) (s:=47) data)) := by
  constructor
  · rw [extend_high data result _ (by decide)]; exact h.precision
  · rw [extend_high data result _ (by decide)]; exact h.numerator
  · rw [extend_high data result _ (by decide)]; exact h.zero
  · rw [extend_high data result _ (by decide)]; exact h.determinant
  · rw [extend_high data result _ (by decide)]; exact h.twice
  · rw [extend_high data result _ (by decide)]; exact h.absolute
  · rw [extend_high data result _ (by decide)]; exact h.remainder
  · rw [extend_high data result _ (by decide)]; exact h.difference

structure Environment (g : Numerator.Geometry) (source : ℕ → ℕ) (b : ℤ) : Prop where
  denominator_bits : ∀ j< g.precision, source (g.determinant+j)≤1
  twice_bits : ∀ j< g.precision, source (g.twice+j)≤1
  zero : ∀ j< g.precision, source (g.zero+j)=0
  remainder_zero : ∀ j< g.precision, source (g.remainder+j)=0
  determinant_value : value source g.determinant g.precision=b.natAbs
  twice_value : value source g.twice g.precision=2*b.natAbs
  nonzero : b≠0
  guard : 4*b.natAbs≤2^g.precision

theorem program_exec {arity w base : ℕ} (e : Circuit.Expression arity)
    (data : Data) (inputs : Fin arity → ℤ) (g : Numerator.Geometry) (b : ℤ)
    (known : Circuit.Represents base g.precision arity (Circuit.integerValues inputs)
      (NaturalData.lower (r:=17) (s:=47) data))
    (positive : 0< g.precision)
    (zero : ∀ slot, arity≤ slot → slot< arity+(e.compile arity).nodes.length →
      ∀ i< g.precision, data.2 (Circuit.slotBase base g.precision slot+i)=0)
    (fits : Fits w (Circuit.resourceBound base g.precision (arity+(e.compile arity).nodes.length)))
    (width : Numerator.Widths g w) (controls : Numerator.Controls g data)
    (output : g.numerator=Circuit.slotBase base g.precision (e.compile arity).output)
    (outside : ∀ slot : Fin 7, slot≠0 → slot≠4 → slot≠6 → ∀ j< g.precision,
      g.base slot+j< Circuit.slotBase base g.precision arity ∨
      Circuit.slotBase base g.precision (arity+(e.compile arity).nodes.length)≤ g.base slot+j)
    (environment : Environment g data.2 b) (signed : Fits g.precision (e.eval inputs)) :
    ∃ result cost, NaturalData.Exec w (program e) data result cost ∧
      cost≤(26*g.precision^2+26*g.precision+16)*(e.compile arity).nodes.length+
        29*g.precision^2+65*g.precision+56 ∧
      (0< result.1 Numerator.G.valid ↔ b∣e.eval inputs) ∧
      result.1 Numerator.G.parity≤1 ∧
      (b∣e.eval inputs → (e.eval inputs/b)%2=(result.1 Numerator.G.parity : ℤ)) ∧
      Numerator.Controls g result ∧
      ∀ address, (address< Circuit.slotBase base g.precision arity ∨
        Circuit.slotBase base g.precision (arity+(e.compile arity).nodes.length)≤ address) →
        (address< g.absolute ∨ g.absolute+g.precision≤ address) →
        (address< g.remainder ∨ g.remainder+g.precision≤ address) →
        (address< g.difference ∨ g.difference+g.precision≤ address) → result.2 address=data.2 address := by
  obtain ⟨circuit,circuitCost,circuitRun,circuitBound,circuitResult,circuitValue,circuitFrame⟩ :=
    e.integer_program_exec (NaturalData.lower (r:=17) (s:=47) data) inputs known positive zero fits
  let middle : Data := circuit.extend (NaturalData.upper (r:=17) (s:=47) data)
  have same (slot : Fin 7) (notN : slot≠0) (notA : slot≠4) (notD : slot≠6)
      (j : ℕ) (within : j< g.precision) : middle.2 (g.base slot+j)=data.2 (g.base slot+j) :=
    circuitFrame _ (outside slot notN notA notD j within)
  have input : Numerator.Input g middle.2 (e.eval inputs) b := by
    constructor
    · exact positive
    · intro j hj
      rw [output]
      exact circuitResult.bits _ (e.output_lt arity (le_refl _)) j hj
    · intro j hj; rw [same 2 (by decide) (by decide) (by decide) j hj]; exact environment.denominator_bits j hj
    · intro j hj; rw [same 3 (by decide) (by decide) (by decide) j hj]; exact environment.twice_bits j hj
    · intro j hj; rw [same 1 (by decide) (by decide) (by decide) j hj]; exact environment.zero j hj
    · intro j hj; rw [same 5 (by decide) (by decide) (by decide) j hj]; exact environment.remainder_zero j hj
    · exact signed
    · simpa [output,middle,Nat.cast_pow] using circuitValue
    · rw [value_congr (fun j hj => same 2 (by decide) (by decide) (by decide) j hj)]
      exact environment.determinant_value
    · rw [value_congr (fun j hj => same 3 (by decide) (by decide) (by decide) j hj)]
      exact environment.twice_value
    · exact environment.nonzero
    · exact environment.guard
  obtain ⟨result,numeratorCost,numeratorRun,numeratorBound,numeratorResult⟩ := Numerator.program_exec g middle (e.eval inputs) b width (controls_extend controls circuit) input
  have full := (NaturalData.call_exec (r:=17) (s:=47) circuitRun).seq numeratorRun
  refine ⟨result,circuitCost+numeratorCost,full,by omega,numeratorResult.valid,numeratorResult.parity_bit,
    (fun divisible => numeratorResult.quotient_parity environment.nonzero divisible),numeratorResult.controls,?_⟩
  intro address outsideCircuit outsideA outsideR outsideD
  rw [numeratorResult.frame address outsideA outsideR outsideD]
  exact circuitFrame address outsideCircuit

end LeanTrominoes.Domino.WordRAM.Binary.Probe
