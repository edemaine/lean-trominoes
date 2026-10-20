/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointXorStep

/-! # Computing the complete parity phase by unrolled digit instructions -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

def phaseTerm {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat) (i : Fin d) : Nat :=
  (((phase i).val+bits i)%2)*2^i.val

def phaseTerms {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat) (indices : List (Fin d)) : Nat :=
  (indices.map (phaseTerm phase bits)).sum

theorem phaseTerms_all {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat) :
    phaseTerms phase bits (List.finRange d)=phaseValue phase bits := by
  exact (Fin.sum_univ_def (phaseTerm phase bits)).symm

theorem xorList_exec {B d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat)
    (indices : List (Fin d)) (data : Data) (small : 2≤B) (two : data.1 R.two=2)
    (dimension : d≤B) (address : data.1 H.parities+d≤B) (power : 2^d≤B)
    (bitBound : ∀ i, bits i≤1) (known : ∀ i, data.2 (data.1 H.parities+i.val)=bits i)
    (room : data.1 R.phase+phaseTerms phase bits indices≤B) :
    ∃ result, Natural.Exec B (xorList phase indices) data result (9*indices.length+1) ∧
      result.2=data.2 ∧ result.1 R.phase=data.1 R.phase+phaseTerms phase bits indices ∧
      ∀ reg : Fin 128, (reg.val<98 ∨ 105<reg.val) → result.1 reg=data.1 reg := by
  induction indices generalizing data with
  | nil =>
    have bound : data.1 R.phase≤B := by simpa [phaseTerms] using room
    refine ⟨data,?_,rfl,by simp [phaseTerms],fun _ _ => rfl⟩
    simpa only [xorList,copy,Nat.mul_zero,Nat.zero_add,NaturalData.set,Function.update_eq_self,List.length_nil,Prod.mk.eta] using
      Natural.Exec.atom (Natural.Step.copy data R.phase R.phase bound)
  | cons i rest ih =>
    have within : i.val≤B := i.isLt.le.trans dimension
    have powerBound : 2^i.val≤B := (pow_le_pow_right₀ (by decide : 1≤(2 : Nat)) i.isLt.le).trans power
    have nextBound : data.1 R.phase+phaseTerm phase bits i≤B := by
      simp only [phaseTerms,List.map_cons,List.sum_cons] at room
      omega
    have first := xorStep_exec phase i data small two within (by have := i.isLt; omega)
      (by rw [known]; exact bitBound i) powerBound (by simpa only [phaseTerm,known] using nextBound)
    let middle := xorState data i.val (phase i).val
    have middlePhase : middle.1 R.phase=data.1 R.phase+phaseTerm phase bits i := by
      simp only [middle,xorState_phase,two,known,phaseTerm]
    have middleTwo : middle.1 R.two=2 := (xorState_fixed data i.val (phase i).val R.two (by decide)).trans two
    have middlePointer : middle.1 H.parities=data.1 H.parities := xorState_fixed data i.val (phase i).val H.parities (by decide)
    obtain ⟨result,later,memory,finalPhase,fixed⟩ := ih middle middleTwo (by rw [middlePointer]; exact address)
      (by intro j; change data.2 (middle.1 H.parities+j.val)=bits j; rw [middlePointer,known])
      (by rw [middlePhase]; simp only [phaseTerms,List.map_cons,List.sum_cons] at room ⊢; omega)
    refine ⟨result,?_,memory,?_,?_⟩
    · simpa only [xorList,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using first.seq later
    · rw [finalPhase,middlePhase]
      simp [phaseTerms,Nat.add_assoc]
    · intro reg outside
      exact (fixed reg outside).trans (xorState_fixed data i.val (phase i).val reg outside)

structure XorResult {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat)
    (before after : Data) : Prop where
  memory : after.2=before.2
  phase : after.1 R.phase=phaseValue phase bits
  two : after.1 R.two=2
  one : after.1 R.one=1
  fixed : ∀ reg : Fin 128, (reg.val<96 ∨ 105<reg.val) → after.1 reg=before.1 reg

theorem xor_exec {B d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat)
    (data : Data) (small : 2≤B) (dimension : d≤B) (address : data.1 H.parities+d≤B) (power : 2^d≤B)
    (bitBound : ∀ i, bits i≤1) (known : ∀ i, data.2 (data.1 H.parities+i.val)=bits i) :
    ∃ result, Natural.Exec B (.seq header (xorList phase (List.finRange d))) data result (9*d+4) ∧ XorResult phase bits data result := by
  have first := Natural.Exec.atom (Natural.Step.constant data R.two 2 small)
  have second := Natural.Exec.atom (Natural.Step.constant (data.set R.two 2) R.one 1 (show 1≤B by omega))
  have third := Natural.Exec.atom (Natural.Step.constant ((data.set R.two 2).set R.one 1) R.phase 0 (Nat.zero_le B))
  have initialized : Natural.Exec B header data (headed data) 3 := first.seq (second.seq third)
  have headedFixed (reg : Fin 128) (outside : reg.val<96 ∨ 105<reg.val) : (headed data).1 reg=data.1 reg := by
    have neTwo : reg≠R.two := by intro eq; have := congrArg Fin.val eq; simp only [R.two] at this; omega
    have neOne : reg≠R.one := by intro eq; have := congrArg Fin.val eq; simp only [R.one] at this; omega
    have nePhase : reg≠R.phase := by intro eq; have := congrArg Fin.val eq; simp only [R.phase] at this; omega
    simp only [headed,NaturalData.set,Function.update_of_ne neTwo,Function.update_of_ne neOne,Function.update_of_ne nePhase]
  have phaseBound := (phaseValue_lt phase bits).le.trans power
  obtain ⟨result,later,memory,finalPhase,fixed⟩ := xorList_exec phase bits (List.finRange d) (headed data) small
    (by simp [headed,NaturalData.set,R.phase,R.one,R.two]) dimension
    (by rw [headedFixed H.parities (by decide)]; exact address) power bitBound
    (by intro i; change data.2 ((headed data).1 H.parities+i.val)=bits i; rw [headedFixed H.parities (by decide),known])
    (by simpa [headed,NaturalData.set,phaseTerms_all,R.phase] using phaseBound)
  refine ⟨result,?_,memory,?_,?_,?_,?_⟩
  · convert initialized.seq later using 1 <;> simp only [List.length_finRange] <;> omega
  · simpa [headed,NaturalData.set,phaseTerms_all,R.phase] using finalPhase
  · rw [fixed R.two (by decide)]
    simp [headed,NaturalData.set,R.phase,R.one,R.two]
  · rw [fixed R.one (by decide)]
    simp [headed,NaturalData.set,R.phase,R.one,R.two]
  · intro reg outside
    exact (fixed reg (by rcases outside with low | high; exact Or.inl (by omega); exact Or.inr high)).trans (headedFixed reg outside)

end LeanTrominoes.Domino.WordRAM.EndpointWriter
