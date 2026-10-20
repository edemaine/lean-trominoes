/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareDetHeaders

/-! # Fresh output arrays after copying the original determinant inputs -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

structure GlobalControls {n d : Nat} (B : BasisData n d) (data : Data) : Prop where
  n : data.1 H.n=n
  precision : data.1 H.precision=WordRAM.precision B
  base : data.1 Reserve.base=inputEnd B
  frontier : data.1 H.frontier=endAddress B
  zero : data.1 H.zero=inputEnd B
  determinant : data.1 H.determinant=inputEnd B+WordRAM.precision B
  twice : data.1 H.twice=inputEnd B+2*WordRAM.precision B
  parities : data.1 H.parities=inputEnd B+3*WordRAM.precision B
  first : data.1 OriginPointers128.H.first=4+d*d*WordRAM.precision B
  second : data.1 OriginPointers128.H.second=4+d*d*WordRAM.precision B

theorem GlobalControls.transport {n d : Nat} {B : BasisData n d} {before after : Data}
    (h : GlobalControls B before) (fixed : ∀ reg : Fin 128, 64≤reg.val → after.1 reg=before.1 reg) : GlobalControls B after := by
  constructor
  all_goals rw [fixed _ (by decide)]
  exact h.n
  exact h.precision
  exact h.base
  exact h.frontier
  exact h.zero
  exact h.determinant
  exact h.twice
  exact h.parities
  exact h.first
  exact h.second

structure DeterminantReady {n d : Nat} (B : BasisData n d) (positive : 0<n) (data : Data) : Prop where
  controls : GlobalControls B data
  known : DeterminantSetup.InputRep (geometry B) (rawInputs B ⟨0,positive⟩ ⟨0,positive⟩) data.2
  fresh : ∀ slot, DeterminantSetup.arity d≤slot → slot<DeterminantSetup.slots d → ∀ i<WordRAM.precision B,
    data.2 (Circuit.slotBase (circuitBase B) (WordRAM.precision B) slot+i)=0
  zero : ∀ i<WordRAM.precision B, data.2 (inputEnd B+i)=0
  original : ∀ address< inputEnd B, data.2 address=inputMemory B address

theorem loaded_ready {n d : Nat} (B : BasisData n d) (positive : 0<n) {data result : Data}
    (ready : SourcesReady B data)
    (known : Circuit.Represents (circuitBase B) (WordRAM.precision B) (d*d+2*d)
      (Circuit.integerValues (rawInputs B ⟨0,positive⟩ ⟨0,positive⟩))
      (NaturalData.lower (r:=17) (s:=47) (Lower result)))
    (frame : ∀ address, (address<circuitBase B ∨ circuitBase B+(d*d+2*d)*WordRAM.precision B≤address) →
      result.2 address=data.2 address)
    (fixed : ∀ reg : Fin 128, 64≤reg.val → result.1 reg=data.1 reg) : DeterminantReady B positive result := by
  have controls : GlobalControls B data := ⟨ready.reserved.n,ready.reserved.precision,ready.reserved.base,
    ready.reserved.frontier,ready.zero,ready.determinant,ready.twice,ready.parities,ready.firstOrigin,ready.secondOrigin⟩
  refine ⟨controls.transport fixed,⟨known.bits,known.value⟩,?_,?_,?_⟩
  · intro slot lower upper i digit
    rw [frame _ (Or.inr (Circuit.slotBase_mono (circuitBase B) (WordRAM.precision B) lower |>.trans (Nat.le_add_right _ _)))]
    apply ready.reserved.zero
    · unfold Circuit.slotBase circuitBase; omega
    · have after := Circuit.digit_before upper digit (base:=circuitBase B)
      have ending : Circuit.slotBase (circuitBase B) (WordRAM.precision B) (DeterminantSetup.slots d)=endAddress B := by
        unfold Circuit.slotBase circuitBase endAddress factor
        ring
      rw [ending] at after
      exact after
  · intro i digit
    rw [frame _ (Or.inl (by unfold circuitBase; nlinarith))]
    apply ready.reserved.zero _ (by omega)
    have positiveL := WordRAM.precision_positive B
    have grow := Nat.mul_le_mul_right (WordRAM.precision B) (show 1≤factor d by unfold factor; omega)
    unfold endAddress
    omega
  · intro address within
    rw [frame _ (Or.inl (by unfold circuitBase; omega))]
    exact ready.reserved.before address within

theorem DeterminantReady.transport {n d : Nat} {B : BasisData n d} {positive : 0<n} {before after : Data}
    (h : DeterminantReady B positive before)
    (fixed : ∀ reg : Fin 128, 64≤reg.val → after.1 reg=before.1 reg)
    (memory : after.2=before.2) : DeterminantReady B positive after := by
  refine ⟨h.controls.transport fixed,?_,?_,?_,?_⟩
  · simpa only [memory] using h.known
  · simpa only [memory] using h.fresh
  · simpa only [memory] using h.zero
  · simpa only [memory] using h.original

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
