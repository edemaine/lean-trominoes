/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantSetupDouble

/-! # Preparing the absolute determinant and twice its magnitude

The caller supplies original basis digits and fresh disjoint workspace. One
fixed program for each dimension evaluates the determinant, takes its binary
absolute value, copies the result, and shifts that copy. All instruction costs
and external memory preservation are included.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
open ComplexityAbstract.RAM

structure Result {d : Nat} (g : Geometry d) (source : Nat → Nat) (z : Int) (result : Data) : Prop where
  controls : Controls g result
  absolute_bits : ∀ i<g.precision, result.2 (g.absolute+i)≤1
  twice_bits : ∀ i<g.precision, result.2 (g.twice+i)≤1
  absolute_value : value result.2 g.absolute g.precision=z.natAbs
  twice_value : value result.2 g.twice g.precision=2*z.natAbs
  frame : ∀ address,
    (address<Circuit.slotBase g.base g.precision (arity d) ∨ Circuit.slotBase g.base g.precision (slots d)≤address) →
    (address<g.absolute ∨ g.absolute+g.precision≤address) →
    (address<g.twice ∨ g.twice+g.precision≤address) → result.2 address=source address

theorem program_preserves (d : Nat) : PreservesHeaders (program d) := by
  intro i high upper
  exact ⟨circuit_preserves d i high upper,absolute_preserves d i high upper,
    copy_preserves i high upper,shift_preserves i high upper⟩

theorem program_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w)
    (controls : Controls g data) (inputs : Fin (arity d) → Int)
    (known : InputRep g inputs data.2) (positive : 0<g.precision)
    (zero : ∀ slot, arity d≤slot → slot<slots d → ∀ i<g.precision,
      data.2 (Circuit.slotBase g.base g.precision slot+i)=0)
    (zeroArray : ∀ i<g.precision, data.2 (g.zero+i)=0)
    (zFits : Fits g.precision ((expression d).eval inputs))
    (doubleRoom : 2*((expression d).eval inputs).natAbs<2^g.precision) :
    ∃ result cost, NaturalData.Exec w (program d) data result cost ∧
      cost≤(26*g.precision^2+26*g.precision+16)*(compiled d).nodes.length+29*g.precision+42 ∧
      Result g data.2 ((expression d).eval inputs) result ∧
      ∀ i : Fin 64, 40≤ i.val → i.val≤60 → result.1 i=data.1 i := by
  obtain ⟨signed,circuitCost,circuitRun,circuitBudget,circuitCorrect⟩ := circuit_exec g data width controls inputs known positive zero
  obtain ⟨absolute,absoluteCost,absoluteRun,absoluteBudget,absoluteCorrect⟩ := absolute_exec g signed width circuitCorrect.controls positive
    ((expression d).eval inputs) circuitCorrect.bits (circuitCorrect.zero zeroArray) zFits circuitCorrect.encoding
  obtain ⟨result,doubleCost,doubleRun,doubleBudget,doubleCorrect⟩ := double_exec g absolute width absoluteCorrect.controls
    absoluteCorrect.bits ((expression d).eval inputs).natAbs absoluteCorrect.magnitude doubleRoom
  have full := circuitRun.seq (absoluteRun.seq doubleRun)
  have apart : Apart g.absolute g.twice g.precision := by
    have separate := g.disjoint 1 2 (by decide)
    rw [g.auxiliary_eq] at separate
    simpa only [show (1 : Fin 3)≠0 by decide,show (2 : Fin 3)≠0 by decide,
      show (2 : Fin 3)≠1 by decide,ite_true,ite_false] using separate
  have retained : ∀ i<g.precision, result.2 (g.absolute+i)=absolute.2 (g.absolute+i) := by
    intro i hi
    exact doubleCorrect.frame _ (apart.outside hi)
  refine ⟨result,circuitCost+(absoluteCost+doubleCost),full,by omega,?_,?_⟩
  · constructor
    · exact doubleCorrect.controls
    · intro i hi; rw [retained i hi]; exact absoluteCorrect.bits i hi
    · exact doubleCorrect.bits
    · rw [value_congr retained]
      exact absoluteCorrect.magnitude
    · exact doubleCorrect.value
    · intro address outsideCircuit outsideAbsolute outsideTwice
      exact (doubleCorrect.frame address outsideTwice).trans
        ((absoluteCorrect.frame address outsideAbsolute).trans (circuitCorrect.frame address outsideCircuit))
  · intro i high upper
    have equal := full.register_eq (program_preserves d i high upper)
    simpa only [NaturalData.word,Int.natCast_inj] using equal

/-- Semantic specialization to the original row-major matrix inputs. The
origins in the two final input blocks can be arbitrary valid digit arrays. -/
theorem determinant_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w)
    (controls : Controls g data) (inputs : Fin (arity d) → Int)
    (matrix : Matrix (Fin d) (Fin d) Int)
    (entries : ∀ i j, inputs (Circuit.rawBasisIndex d i j)=matrix i j)
    (known : InputRep g inputs data.2) (positive : 0<g.precision)
    (zero : ∀ slot, arity d≤slot → slot<slots d → ∀ i<g.precision,
      data.2 (Circuit.slotBase g.base g.precision slot+i)=0)
    (zeroArray : ∀ i<g.precision, data.2 (g.zero+i)=0)
    (detFits : Fits g.precision matrix.det) (room : 4*matrix.det.natAbs≤2^g.precision) :
    ∃ result cost, NaturalData.Exec w (program d) data result cost ∧
      cost≤(26*g.precision^2+26*g.precision+16)*(compiled d).nodes.length+29*g.precision+42 ∧
      Result g data.2 matrix.det result ∧
      ∀ i : Fin 64, 40≤ i.val → i.val≤60 → result.1 i=data.1 i := by
  have meaning : (expression d).eval inputs=matrix.det := Circuit.rawDeterminantCircuit_eval inputs matrix entries
  have positiveCapacity : 0<2^g.precision := Nat.two_pow_pos _
  have doubleRoom : 2*matrix.det.natAbs<2^g.precision := by omega
  simpa only [meaning] using program_exec g data width controls inputs known positive zero zeroArray
    (by rw [meaning]; exact detFits) (by rw [meaning]; exact doubleRoom)

end LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
