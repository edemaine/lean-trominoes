/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointProgram

/-! # Nine bounded-word instructions compute one phase XOR digit -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM
attribute [local simp] H.parities R.two R.one R.coordinate R.address R.bit R.sum R.xor R.weight R.term R.phase
  constant add mul copy xor1 xor2 xor3 xor4 xor5 xor6 xor7 xor8 xorState NaturalData.set

theorem xorStep_exec {B d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (i : Fin d) (data : Data)
    (small : 2≤B) (two : data.1 R.two=2) (index : i.val≤B)
    (address : data.1 H.parities+i.val≤B) (bit : data.2 (data.1 H.parities+i.val)≤1)
    (weight : 2^i.val≤B)
    (accumulated : data.1 R.phase+(((phase i).val+data.2 (data.1 H.parities+i.val))%2)*2^i.val≤B) :
    Natural.Exec B (xorStep phase i) data (xorState data i.val (phase i).val) 9 := by
  dsimp only [H.parities,R.two,R.phase] at *
  have phaseBound : (phase i).val≤1 := by have := (phase i).isLt; omega
  have digitBound : ((phase i).val+data.2 (data.1 H.parities+i.val))%2≤1 := by omega
  have termBound : (((phase i).val+data.2 (data.1 H.parities+i.val))%2)*2^i.val≤B := by
    have bound : (((phase i).val+data.2 (data.1 H.parities+i.val))%2)*2^i.val≤2^i.val := by
      simpa only [one_mul] using Nat.mul_le_mul_right (2^i.val) digitBound
    exact bound.trans weight
  have first : Natural.Exec B (constant R.coordinate i.val) data (xor1 data i.val) 1 := Natural.Exec.atom (Natural.Step.constant _ _ _ index)
  have second : Natural.Exec B (add R.address H.parities R.coordinate) (xor1 data i.val) (xor2 data i.val) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.add (bound:=B) (xor1 data i.val) R.address H.parities R.coordinate (by simpa using address))
  have third : Natural.Exec B (.atom (.load R.bit R.address)) (xor2 data i.val) (xor3 data i.val) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.load (bound:=B) (xor2 data i.val) R.bit R.address (by simpa using address) (by simpa using bit.trans (show 1≤B by omega)))
  have fourth : Natural.Exec B (constant R.sum (phase i).val) (xor3 data i.val) (xor4 data i.val (phase i).val) 1 :=
    Natural.Exec.atom (Natural.Step.constant _ _ _ (phaseBound.trans (by omega)))
  have fifth : Natural.Exec B (add R.sum R.sum R.bit) (xor4 data i.val (phase i).val) (xor5 data i.val (phase i).val) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.add (bound:=B) (xor4 data i.val (phase i).val) R.sum R.sum R.bit (by simp; omega))
  have sixth : Natural.Exec B (.atom (.arithmetic .mod R.xor R.sum R.two)) (xor5 data i.val (phase i).val) (xor6 data i.val (phase i).val) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.mod (bound:=B) (xor5 data i.val (phase i).val) R.xor R.sum R.two (by simp [two]; omega))
  have seventh : Natural.Exec B (constant R.weight (2^i.val)) (xor6 data i.val (phase i).val) (xor7 data i.val (phase i).val) 1 := Natural.Exec.atom (Natural.Step.constant _ _ _ weight)
  have eighth : Natural.Exec B (mul R.term R.xor R.weight) (xor7 data i.val (phase i).val) (xor8 data i.val (phase i).val) 1 := by
    simpa [two] using Natural.Exec.atom (Natural.Step.mul (bound:=B) (xor7 data i.val (phase i).val) R.term R.xor R.weight (by simpa [two] using termBound))
  have ninth : Natural.Exec B (add R.phase R.phase R.term) (xor8 data i.val (phase i).val) (xorState data i.val (phase i).val) 1 := by
    simpa [two] using Natural.Exec.atom (Natural.Step.add (bound:=B) (xor8 data i.val (phase i).val) R.phase R.phase R.term (by simpa [two] using accumulated))
  simpa only [xorStep,Nat.reduceAdd] using first.seq (second.seq (third.seq (fourth.seq (fifth.seq (sixth.seq (seventh.seq (eighth.seq ninth)))))))

theorem xorState_memory (data : Data) (i bit : Nat) : (xorState data i bit).2=data.2 := rfl

theorem xorState_fixed (data : Data) (i bit : Nat) (reg : Fin 128)
    (outside : reg.val<98 ∨ 105<reg.val) : (xorState data i bit).1 reg=data.1 reg := by
  have different (dst : Fin 128) (lower : 98≤dst.val) (upper : dst.val≤105) : reg≠dst := by
    intro same; have equal := congrArg Fin.val same; omega
  simp only [xorState,xor8,xor7,xor6,xor5,xor4,xor3,xor2,xor1,NaturalData.set]
  simp only [Function.update_of_ne (different R.phase (by decide) (by decide)),
    Function.update_of_ne (different R.term (by decide) (by decide)),
    Function.update_of_ne (different R.weight (by decide) (by decide)),
    Function.update_of_ne (different R.xor (by decide) (by decide)),
    Function.update_of_ne (different R.sum (by decide) (by decide)),
    Function.update_of_ne (different R.bit (by decide) (by decide)),
    Function.update_of_ne (different R.address (by decide) (by decide)),
    Function.update_of_ne (different R.coordinate (by decide) (by decide))]

theorem xorState_phase (data : Data) (i bit : Nat) :
    (xorState data i bit).1 R.phase=data.1 R.phase+((bit+data.2 (data.1 H.parities+i))%data.1 R.two)*2^i := by simp

end LeanTrominoes.Domino.WordRAM.EndpointWriter
