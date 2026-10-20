/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantSetupCalls

/-! # Actual execution of the determinant circuit on caller input digits -/
namespace LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
open ComplexityAbstract.RAM

structure InputRep {d : Nat} (g : Geometry d) (inputs : Fin (arity d) → Int) (memory : Nat → Nat) : Prop where
  bits : ∀ slot<arity d, ∀ i<g.precision, memory (Circuit.slotBase g.base g.precision slot+i)≤1
  value : ∀ slot<arity d,
    (Binary.value memory (Circuit.slotBase g.base g.precision slot) g.precision : ZMod (2^g.precision))=
      Circuit.integerValues inputs slot

structure CircuitResult {d : Nat} (g : Geometry d) (source : Nat → Nat) (z : Int) (result : Data) : Prop where
  controls : Controls g result
  bits : ∀ i<g.precision, result.2 (g.signed+i)≤1
  encoding : (value result.2 g.signed g.precision : Int)=z%(2^g.precision : Nat)
  frame : ∀ address, (address<Circuit.slotBase g.base g.precision (arity d) ∨
    Circuit.slotBase g.base g.precision (slots d)≤address) → result.2 address=source address

theorem circuit_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w)
    (controls : Controls g data) (inputs : Fin (arity d) → Int)
    (known : InputRep g inputs data.2) (positive : 0<g.precision)
    (zero : ∀ slot, arity d≤slot → slot<slots d → ∀ i<g.precision,
      data.2 (Circuit.slotBase g.base g.precision slot+i)=0) :
    ∃ result cost, NaturalData.Exec w (circuitCode d) data result cost ∧
      cost≤(26*g.precision^2+26*g.precision+16)*(compiled d).nodes.length+4 ∧
      CircuitResult g data.2 ((expression d).eval inputs) result := by
  have args := circuitPrepared_controls g data controls
  have before : Circuit.Represents g.base g.precision (arity d) (Circuit.integerValues inputs)
      (NaturalData.lower (r:=17) (s:=47) (circuitPrepared data)) := by
    exact ⟨args.1,args.2,known.bits,known.value⟩
  obtain ⟨small,cost,run,budget,correct,encoded,frame⟩ := (expression d).integer_program_exec
    (NaturalData.lower (r:=17) (s:=47) (circuitPrepared data)) inputs before positive
    (by simpa only [circuitPrepared,Assignments.state_memory,NaturalData.lower,arity,slots,compiled] using zero) width.circuit
  have call := NaturalData.call_exec (r:=17) (s:=47) run
  have full := (circuitSetup_exec g data width controls).seq call
  change cost≤(26*g.precision^2+26*g.precision+16)*(compiled d).nodes.length+1 at budget
  refine ⟨_,3+cost,full,by omega,?_⟩
  constructor
  · exact controls.after full (circuit_preserves d)
  · exact correct.bits _ ((expression d).output_lt (arity d) (le_refl _))
  · exact encoded
  · simpa only [NaturalData.lower,circuitPrepared,Assignments.state_memory,NaturalData.extend_memory,arity,slots,compiled] using frame

theorem Geometry.external_aux {d : Nat} (g : Geometry d) (slot : Fin 3) (i : Nat) (within : i<g.precision) :
    g.auxiliary slot+i<Circuit.slotBase g.base g.precision (arity d) ∨
      Circuit.slotBase g.base g.precision (slots d)≤g.auxiliary slot+i := by
  have bound := g.external slot
  have grow : g.base≤Circuit.slotBase g.base g.precision (arity d) := by unfold Circuit.slotBase; omega
  unfold Circuit.slotBase at *
  omega

theorem CircuitResult.zero {d : Nat} {g : Geometry d} {source : Nat → Nat} {z : Int} {result : Data}
    (h : CircuitResult g source z result) (zeros : ∀ i<g.precision, source (g.zero+i)=0) :
    ∀ i<g.precision, result.2 (g.zero+i)=0 := by
  intro i hi
  have outside := g.external_aux 0 i hi
  rw [g.auxiliary_eq] at outside
  simp only [ite_true] at outside
  rw [h.frame _ outside]
  exact zeros i hi

end LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
