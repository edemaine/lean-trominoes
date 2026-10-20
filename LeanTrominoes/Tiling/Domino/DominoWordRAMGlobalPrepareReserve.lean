/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareHeader

/-! # Checked allocation of the shared determinant and parity workspace -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

noncomputable def reservedData {n d : Nat} (B : BasisData n d) : Data :=
  Reserve.saved ((Reserve.prepared (headerState (WordRAM.initialData 128 B)) (factor d)).allocated
    (inputEnd B) (factor d*WordRAM.precision B))

structure Reserved {n d : Nat} (B : BasisData n d) (data : Data) : Prop where
  n : data.1 H.n=n
  precision : data.1 H.precision=WordRAM.precision B
  base : data.1 Reserve.base=inputEnd B
  frontier : data.1 H.frontier=endAddress B
  memory : data.2=NaturalData.clear (inputMemory B) (inputEnd B) (factor d*WordRAM.precision B)

theorem reserve_exec {n d w : Nat} (B : BasisData n d) (width : Fits w (resourceBound B)) :
    NaturalData.Exec w (.seq header (Reserve.program (factor d))) (WordRAM.initialData 128 B) (reservedData B)
      (8+(4*(factor d*WordRAM.precision B)+12)) ∧ Reserved B (reservedData B) := by
  have controls := header_controls B
  have headerL : (headerState (WordRAM.initialData 128 B)).1 Reserve.precision=WordRAM.precision B := controls.2.1
  have headerI : (headerState (WordRAM.initialData 128 B)).1 Reserve.frontier=inputEnd B := controls.2.2
  obtain ⟨result,run,front,base,memory,registers,equal⟩ := Reserve.program_exec
    (headerState (WordRAM.initialData 128 B)) (factor d)
    (Allocation.nat_fits_le width (by unfold resourceBound; omega))
    (by rw [headerL]; apply Allocation.nat_fits_le width; unfold resourceBound; omega)
    (by rw [headerL,headerI]; exact Allocation.nat_fits_le width (resource_end B))
    (Allocation.nat_fits_le width (by have := resource_small B; omega))
  have same : result=reservedData B := by simpa only [reservedData,headerL,headerI] using equal
  rw [same] at run front base memory registers
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have full := (header_exec B width).seq run
    simpa only [headerL] using full
  · rw [registers _ (by decide) (by decide) (by decide)]
    exact controls.1
  · rw [registers _ (by decide) (by decide) (by decide)]
    exact controls.2.1
  · simpa only [headerI] using base
  · simpa only [headerL,headerI,endAddress] using front
  · rw [headerI,headerL] at memory
    simpa only [header_memory,WordRAM.initialData] using memory

theorem reserve_after_header_exec {n d w : Nat} (B : BasisData n d) (width : Fits w (resourceBound B)) :
    NaturalData.Exec w (Reserve.program (factor d)) (headerState (WordRAM.initialData 128 B)) (reservedData B)
      (4*(factor d*WordRAM.precision B)+12) := by
  have controls := header_controls B
  have headerL : (headerState (WordRAM.initialData 128 B)).1 Reserve.precision=WordRAM.precision B := controls.2.1
  have headerI : (headerState (WordRAM.initialData 128 B)).1 Reserve.frontier=inputEnd B := controls.2.2
  obtain ⟨result,run,front,base,memory,registers,equal⟩ := Reserve.program_exec
    (headerState (WordRAM.initialData 128 B)) (factor d)
    (Allocation.nat_fits_le width (by unfold resourceBound; omega))
    (by rw [headerL]; apply Allocation.nat_fits_le width; unfold resourceBound; omega)
    (by rw [headerL,headerI]; exact Allocation.nat_fits_le width (resource_end B))
    (Allocation.nat_fits_le width (by have := resource_small B; omega))
  have same : result=reservedData B := by simpa only [reservedData,headerL,headerI] using equal
  rw [same] at run
  simpa only [headerL] using run

theorem Reserved.before {n d : Nat} {B : BasisData n d} {data : Data} (h : Reserved B data)
    (address : Nat) (before : address< inputEnd B) : data.2 address=inputMemory B address := by
  rw [h.memory,Reserve.clear_apply,if_neg (by omega)]

theorem Reserved.zero {n d : Nat} {B : BasisData n d} {data : Data} (h : Reserved B data)
    (address : Nat) (lower : inputEnd B≤address) (upper : address<endAddress B) : data.2 address=0 := by
  rw [h.memory,Reserve.clear_apply,if_pos]
  exact ⟨lower,by simpa only [endAddress] using upper⟩

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
