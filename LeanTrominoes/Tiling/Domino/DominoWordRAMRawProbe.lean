/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRawReady

/-! # A bounded-word lattice-coordinate probe on the original integer input -/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM
open Binary
variable {n d : ℕ}

noncomputable def rawProbeProgram (d : ℕ) (direction coordinate : Fin d) : Structured.Code 64 :=
  .seq (SourceLoad.completeProgram d) (Probe.program (Circuit.rawNumeratorCircuit d direction coordinate))

theorem rawNumerator_fits (B : BasisData n d) (u v : Fin n) (direction coordinate : Fin d) :
    Fits (precision B) ((Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)) := by
  rw [rawNumerator_eval]
  have vector : (fun j => B.origin u j-B.origin v j+(if j=direction then 1 else 0))=
      B.origin u+unit direction-B.origin v := by
    funext j
    by_cases equal : j=direction <;> simp [unit,Pi.single_apply,equal] <;> ring
  rw [vector]
  exact LeanTrominoes.WordBounds.fits_mono (by unfold precision; omega) (numerator_fits B u v direction coordinate)

theorem raw_probe_exec {w base : ℕ} (B : BasisData n d) (u v : Fin n) (direction coordinate : Fin d)
    (data : SourceLoad.Data) (g : Numerator.Geometry)
    (length : g.precision=precision B)
    (sourceControls : SourceLoad.Controls (sourceLayout B u v base) data)
    (original : ∀ block : Fin 3, ∀ slot< SourceLoad.count d block, ∀ i< precision B,
      data.2 ((sourceLayout B u v base).source block+slot*precision B+i)=
        inputMemory B ((sourceLayout B u v base).source block+slot*precision B+i))
    (sourceOutside : ∀ block : Fin 3, ∀ slot< SourceLoad.count d block, ∀ i< precision B,
      (sourceLayout B u v base).source block+slot*precision B+i< base ∨
        base+(d*d+2*d)*precision B≤(sourceLayout B u v base).source block+slot*precision B+i)
    (sourceFits : ∀ block : Fin 3, Fits w (BatchCopy.bound ((sourceLayout B u v base).source block) base (precision B) 0
      (SourceLoad.start d block) (SourceLoad.count d block)))
    (controls : Numerator.Controls g data) (width : Numerator.Widths g w)
    (environment : Probe.Environment g data.2 B.basis.det)
    (output : g.numerator=Circuit.slotBase base g.precision
      ((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).output)
    (outside : ∀ slot : Fin 7, slot≠0 → slot≠4 → slot≠6 → ∀ j< g.precision,
      g.base slot+j< base ∨ Circuit.slotBase base g.precision
        (d*d+2*d+((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length)≤ g.base slot+j)
    (zero : ∀ slot, d*d+2*d≤ slot → slot< d*d+2*d+((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length →
      ∀ i< g.precision, data.2 (Circuit.slotBase base g.precision slot+i)=0)
    (fits : Fits w (Circuit.resourceBound base g.precision
      (d*d+2*d+((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length))) :
    ∃ result cost, NaturalData.Exec w (rawProbeProgram d direction coordinate) data result cost ∧
      cost≤(26*g.precision^2+26*g.precision+16)*
        ((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length+
        29*g.precision^2+65*g.precision+73+(7*g.precision+11)*(d*d+2*d) ∧
      (0< result.1 Numerator.G.valid ↔ B.basis.det∣
        (Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)) ∧
      result.1 Numerator.G.parity≤1 ∧
      (B.basis.det∣(Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v) →
        ((Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)/B.basis.det)%2=
          (result.1 Numerator.G.parity : ℤ)) ∧ Numerator.Controls g result ∧
      ∀ address, (address< base ∨ Circuit.slotBase base g.precision
        (d*d+2*d+((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length)≤ address) →
        (address< g.absolute ∨ g.absolute+g.precision≤ address) →
        (address< g.remainder ∨ g.remainder+g.precision≤ address) →
        (address< g.difference ∨ g.difference+g.precision≤ address) → result.2 address=data.2 address := by
  let e := Circuit.rawNumeratorCircuit d direction coordinate
  let arity := d*d+2*d
  have positive : 0< g.precision := by rw [length]; unfold precision; omega
  obtain ⟨loaded,loadCost,loadRun,loadBound,known,loadFrame⟩ := raw_source_exec B u v base data sourceControls original sourceOutside sourceFits
  have prefixFrame (address : ℕ) (beforeOrAfter : address< base ∨ Circuit.slotBase base g.precision (arity+(e.compile arity).nodes.length)≤ address) :
      loaded.2 address=data.2 address := by
    apply loadFrame
    rcases beforeOrAfter with before | after
    · exact Or.inl before
    · right
      have grow := Circuit.slotBase_mono base g.precision (show arity≤ arity+(e.compile arity).nodes.length by omega)
      change base+arity*g.precision≤_ at grow
      rw [←length]
      exact grow.trans after
  have same (slot : Fin 7) (notN : slot≠0) (notA : slot≠4) (notD : slot≠6)
      (j : ℕ) (within : j< g.precision) : loaded.2 (g.base slot+j)=data.2 (g.base slot+j) :=
    prefixFrame _ (outside slot notN notA notD j within)
  have loadedEnvironment : Probe.Environment g loaded.2 B.basis.det := by
    constructor
    · intro j hj; rw [same 2 (by decide) (by decide) (by decide) j hj]; exact environment.denominator_bits j hj
    · intro j hj; rw [same 3 (by decide) (by decide) (by decide) j hj]; exact environment.twice_bits j hj
    · intro j hj; rw [same 1 (by decide) (by decide) (by decide) j hj]; exact environment.zero j hj
    · intro j hj; rw [same 5 (by decide) (by decide) (by decide) j hj]; exact environment.remainder_zero j hj
    · rw [value_congr (fun j hj => same 2 (by decide) (by decide) (by decide) j hj)]; exact environment.determinant_value
    · rw [value_congr (fun j hj => same 3 (by decide) (by decide) (by decide) j hj)]; exact environment.twice_value
    · exact environment.nonzero
    · exact environment.guard
  have loadedZero : ∀ slot, arity≤ slot → slot< arity+(e.compile arity).nodes.length →
      ∀ i< g.precision, loaded.2 (Circuit.slotBase base g.precision slot+i)=0 := by
    intro slot hs he i hi
    rw [loadFrame _ (Or.inr (by
      rw [←length]
      have grow := Circuit.slotBase_mono base g.precision hs
      exact grow.trans (Nat.le_add_right _ _)))]
    exact zero slot hs he i hi
  obtain ⟨result,probeCost,probeRun,probeBound,valid,bit,parity,resultControls,frame⟩ := Probe.program_exec e loaded
    (rawInputs B u v) g B.basis.det (by rw [length]; exact known) positive loadedZero fits width
    (controls.after loadRun (SourceLoad.preservesHeaders d)) output
    (by intro slot hn ha hd j hj; rcases outside slot hn ha hd j hj with before | after
        · left; exact lt_of_lt_of_le before (Nat.le_add_right _ _)
        · right; exact after)
    loadedEnvironment (by rw [length]; exact rawNumerator_fits B u v direction coordinate)
  refine ⟨result,loadCost+probeCost,loadRun.seq probeRun,?_,valid,bit,parity,resultControls,?_⟩
  · rw [←length] at loadBound
    dsimp only [e] at probeBound
    omega
  · intro address outsideCircuit outsideA outsideR outsideD
    rw [frame address (by
      rcases outsideCircuit with before | after
      · left; exact lt_of_lt_of_le before (Nat.le_add_right _ _)
      · right; exact after) outsideA outsideR outsideD]
    exact prefixFrame address outsideCircuit

end LeanTrominoes.Domino.WordRAM
