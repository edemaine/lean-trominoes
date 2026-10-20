/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitPointers

/-! # Checked arithmetic nodes with runtime binary-array addresses -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

abbrev slotBase (base length slot : ℕ) : ℕ := base+slot*length

def arithmeticProgram (op : Operation) (first second output : ℕ) : Code :=
  .seq (prepareProgram first second output) (op.code.embed 1)

structure NodeResult (op : Operation) (base length first second output : ℕ)
    (source : ℕ → ℕ) (data : Data) : Prop where
  base_eq : data.1 baseRegister=base
  length_eq : data.1 (low Reg.length)=length
  bits : ∀ i< length, data.2 (slotBase base length output+i)≤1
  frame : ∀ address, (address< slotBase base length output ∨ slotBase base length output+length≤address) →
    data.2 address=source address
  value : (Binary.value data.2 (slotBase base length output) length : ZMod (2^length))=
    op.eval (Binary.value source (slotBase base length first) length : ZMod (2^length))
      (Binary.value source (slotBase base length second) length : ZMod (2^length))

/-- A fixed circuit node computes all runtime pointers, executes its digit
routine, and preserves the common base and precision for the next node. -/
theorem arithmetic_exec {w base length slots : ℕ} (op : Operation) (data : Data)
    (first second output : ℕ) (baseEq : data.1 baseRegister=base)
    (lengthEq : data.1 (low Reg.length)=length)
    (firstBound : first≤slots) (secondBound : second≤slots) (outputBound : output≤slots)
    (firstNe : output≠first) (secondNe : output≠second)
    (firstBits : ∀ i< length, data.2 (slotBase base length first+i)≤1)
    (secondBits : ∀ i< length, data.2 (slotBase base length second+i)≤1)
    (zero : ∀ i< length, data.2 (slotBase base length output+i)=0)
    (fits : Fits w (resourceBound base length slots)) :
    ∃ result cost, NaturalData.Exec w (arithmeticProgram op first second output) data result cost ∧
      cost≤26*length^2+26*length+16 ∧ NodeResult op base length first second output data.2 result := by
  let geometry : Multiply.Layout :=
    ⟨slotBase base length first,slotBase base length second,slotBase base length output,length,
      fun _ hi _ hj => slot_disjoint firstNe hi hj,fun _ hi _ hj => slot_disjoint secondNe hi hj⟩
  let ready := prepared data first second output
  let arguments : Binary.Data := NaturalData.lower (r:=16) (s:=1) ready
  have firstEq : arguments.1 Reg.first=geometry.first := by
    simpa only [arguments,NaturalData.lower,geometry,baseEq,lengthEq] using prepared_first data first second output
  have secondEq : arguments.1 Reg.second=geometry.second := by
    simpa only [arguments,NaturalData.lower,geometry,baseEq,lengthEq] using prepared_second data first second output
  have outputEq : arguments.1 Reg.output=geometry.output := by
    simpa only [arguments,NaturalData.lower,geometry,baseEq,lengthEq] using prepared_output data first second output
  have precisionEq : arguments.1 Reg.length=geometry.length := by
    simpa only [arguments,NaturalData.lower,geometry] using (prepared_length data first second output).trans lengthEq
  have small : Fits w (3:ℕ) := Allocation.nat_fits_le fits (by unfold resourceBound; omega)
  have precisionFits : Fits w length := Allocation.nat_fits_le fits (by unfold resourceBound; nlinarith)
  obtain ⟨result,cost,run,bound,correct⟩ := operation_exec op geometry arguments
    firstEq secondEq outputEq precisionEq firstBits secondBits zero small
    (resource_end_fits fits firstBound) (resource_end_fits fits secondBound)
    (resource_end_fits fits outputBound) precisionFits
  change cost≤26*length^2+26*length+7 at bound
  have setup := prepare_exec data first second output baseEq lengthEq firstBound secondBound outputBound fits
  have call := NaturalData.call_exec (s:=1) run
  refine ⟨result.extend (NaturalData.upper (r:=16) (s:=1) ready),9+cost,setup.seq call,by omega,?_⟩
  constructor
  · change (result.extend (NaturalData.upper (r:=16) (s:=1) ready)).1 ((0 : Fin 1).natAdd 16)=base
    rw [NaturalData.extend_right]
    exact (prepared_base data first second output).trans baseEq
  · simpa only [low,NaturalData.extend_left] using correct.length
  · exact correct.bits
  · exact correct.frame
  · exact correct.value

end LeanTrominoes.Domino.WordRAM.Binary.Circuit
