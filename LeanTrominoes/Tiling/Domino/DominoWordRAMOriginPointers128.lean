/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMOriginPointer128

/-! # Both original-origin addresses in eleven actual instructions -/
namespace LeanTrominoes.Domino.WordRAM.OriginPointers128
open ComplexityAbstract.RAM

structure Result (d : Nat) (before after : Data) : Prop where
  memory : after.2=before.2
  first : after.1 H.first=4+(d*d+before.1 H.u*d)*before.1 H.precision
  second : after.1 H.second=4+(d*d+before.1 H.v*d)*before.1 H.precision
  fixed : ∀ reg : Fin 128, (reg.val<96 ∨ 98<reg.val) → reg≠H.first → reg≠H.second → after.1 reg=before.1 reg

attribute [local simp] H.u H.v H.precision H.first H.second R.dimension R.square R.four NaturalData.set

theorem header_exec {bound : Nat} (data : Data) (d : Nat) (constants : d*d+d+4≤bound) :
    Natural.Exec bound (header d) data (headed data d) 3 := by
  have first := Natural.Exec.atom (Natural.Step.constant data R.dimension d (show d≤bound by omega))
  have second := Natural.Exec.atom (Natural.Step.constant (data.set R.dimension d) R.square (d*d) (show d*d≤bound by omega))
  have third := Natural.Exec.atom (Natural.Step.constant ((data.set R.dimension d).set R.square (d*d)) R.four 4 (show 4≤bound by omega))
  exact first.seq (second.seq third)

theorem headed_fixed (data : Data) (d : Nat) (reg : Fin 128) (outside : reg.val<96 ∨ 98<reg.val) :
    (headed data d).1 reg=data.1 reg := by
  have dn : reg≠R.dimension := by intro same; have := congrArg Fin.val same; simp at this; omega
  have sn : reg≠R.square := by intro same; have := congrArg Fin.val same; simp at this; omega
  have fn : reg≠R.four := by intro same; have := congrArg Fin.val same; simp at this; omega
  simp only [headed,NaturalData.set,Function.update_of_ne dn,Function.update_of_ne sn,Function.update_of_ne fn]

theorem program_native {bound d : Nat} (data : Data) (positive : 0<data.1 H.precision)
    (constants : d*d+d+4≤bound)
    (firstAddress : 4+(d*d+data.1 H.u*d)*data.1 H.precision≤bound)
    (secondAddress : 4+(d*d+data.1 H.v*d)*data.1 H.precision≤bound) :
    ∃ result, Natural.Exec bound (program d) data result 11 ∧ Result d data result := by
  let ready := headed data d
  have first := pointer_exec (bound:=bound) (d:=d) (length:=data.1 H.precision) ready H.first H.u (by decide)
    (by simp [ready,headed]) (by simp [ready,headed]) (by simp [ready,headed])
    (show ready.1 H.precision=data.1 H.precision by exact headed_fixed data d H.precision (by decide)) positive
    (by simpa [ready,headed,Nat.add_comm] using firstAddress)
  let middle := pointerState ready H.first H.u
  have second := pointer_exec (bound:=bound) (d:=d) (length:=data.1 H.precision) middle H.second H.v (by decide)
    (by rw [pointerState_fixed ready H.first H.u R.dimension (by decide)]; simp [ready,headed])
    (by rw [pointerState_fixed ready H.first H.u R.square (by decide)]; simp [ready,headed])
    (by rw [pointerState_fixed ready H.first H.u R.four (by decide)]; simp [ready,headed])
    (show middle.1 H.precision=data.1 H.precision by
      rw [pointerState_fixed ready H.first H.u H.precision (by decide),headed_fixed data d H.precision (by decide)]) positive
    (by rw [pointerState_fixed ready H.first H.u H.v (by decide),headed_fixed data d H.v (by decide)]
        simpa only [Nat.add_comm] using secondAddress)
  let result := pointerState middle H.second H.v
  refine ⟨result,(header_exec data d constants).seq (first.seq second),rfl,?_,?_,?_⟩
  · rw [pointerState_fixed middle H.second H.v H.first (by decide),pointerState_value]
    simp [ready,headed,Nat.add_comm]
  · rw [pointerState_value,pointerState_fixed ready H.first H.u H.v (by decide),
      pointerState_fixed ready H.first H.u R.dimension (by decide),pointerState_fixed ready H.first H.u R.square (by decide),
      pointerState_fixed ready H.first H.u H.precision (by decide),pointerState_fixed ready H.first H.u R.four (by decide)]
    simp [ready,headed,Nat.add_comm]
  · intro reg outside firstNe secondNe
    exact (pointerState_fixed middle H.second H.v reg secondNe).trans
      ((pointerState_fixed ready H.first H.u reg firstNe).trans (headed_fixed data d reg outside))

/-- Every multiplication, addition and constant load is checked in the actual
bounded-word machine; unrelated caller registers and all memory survive. -/
theorem program_exec {bound w d : Nat} (data : Data) (width : Fits w bound)
    (positive : 0<data.1 H.precision) (constants : d*d+d+4≤bound)
    (firstAddress : 4+(d*d+data.1 H.u*d)*data.1 H.precision≤bound)
    (secondAddress : 4+(d*d+data.1 H.v*d)*data.1 H.precision≤bound) :
    ∃ result, NaturalData.Exec w (program d) data result 11 ∧ Result d data result := by
  obtain ⟨result,run,correct⟩ := program_native data positive constants firstAddress secondAddress
  exact ⟨result,run.compiles width,correct⟩

end LeanTrominoes.Domino.WordRAM.OriginPointers128
