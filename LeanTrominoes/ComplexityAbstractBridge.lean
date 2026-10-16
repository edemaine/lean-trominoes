/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract
import LeanTrominoes.Complexity.NP

/-! # Correspondence for the public complexity definitions

The public notions use encoding functions and Mathlib machines directly.
These lemmas identify them with the development's bundled certificates.
-/

namespace LeanTrominoes.ComplexityAbstractBridge

open Computability

theorem polyTime_iff {A B Γ Δ : Type} [Finite Δ]
    (input : A → List Γ) (output : B → List Δ) (f : A → B) :
    ComplexityAbstract.PolyTime input output f ↔
      Nonempty (Complexity.FiniteAlphabetComputableInPolyTime input output f) := by
  constructor
  · rintro ⟨computer⟩
    exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime computer⟩
  · rintro ⟨computer⟩
    exact ⟨computer.toTM2ComputableInPolyTime⟩

theorem reduces_iff {A B : Type} (input : FiniteEncoding A) (output : FiniteEncoding B)
    (p : A → Prop) (q : B → Prop) :
    ComplexityAbstract.Reduces input.encode output.encode p q ↔
      Complexity.PolyTimeManyOneReducible input output p q := by
  simp only [ComplexityAbstract.Reduces, Complexity.PolyTimeManyOneReducible, polyTime_iff]

theorem inNP_iff {A : Type} (e : FiniteEncoding A) (p : A → Prop) :
    ComplexityAbstract.InNP e.encode p ↔ Complexity.InNP e p := by
  constructor
  · rintro ⟨verify, computer, bound, correct⟩
    obtain ⟨machine⟩ := (polyTime_iff _ _ _).mp computer
    exact ⟨{ verify := verify, computer := machine, witnessBound := bound, correct := correct }⟩
  · rintro ⟨verifier⟩
    exact ⟨verifier.verify, ⟨verifier.computer.toTM2ComputableInPolyTime⟩,
      verifier.witnessBound, verifier.correct⟩

theorem inPSPACE_iff {A : Type} (e : FiniteEncoding A) (p : A → Prop) :
    ComplexityAbstract.InPSPACE e.encode p ↔ Complexity.InPSPACE e p := by
  constructor
  · rintro ⟨d⟩
    exact ⟨{ toTM2ComputableAux := d.toTM2ComputableAux
             stackAlphabetFinite := d.stackAlphabetFinite
             result := d.result
             correct := d.correct
             outputs := d.outputs
             space := d.space
             space_le := d.space_le }⟩
  · rintro ⟨d⟩
    exact ⟨{ toTM2ComputableAux := d.toTM2ComputableAux
             stackAlphabetFinite := d.stackAlphabetFinite
             result := d.result
             correct := d.correct
             outputs := d.outputs
             space := d.space
             space_le := d.space_le }⟩

theorem npHard_iff {A : Type} (e : FiniteEncoding A) (p : A → Prop) :
    ComplexityAbstract.NPHard e.encode p ↔ Complexity.NPHard e p := by
  constructor
  · intro hard B input q member
    exact (reduces_iff input e q p).mp
      (hard input.encoding q ((inNP_iff input q).mpr member))
  · intro hard B Γ _ input q member
    let source : FiniteEncoding B := ⟨Γ, inferInstance, input⟩
    exact (reduces_iff source e q p).mpr
      (hard source q ((inNP_iff source q).mp member))

theorem pspaceHard_iff {A : Type} (e : FiniteEncoding A) (p : A → Prop) :
    ComplexityAbstract.PSPACEHard e.encode p ↔ Complexity.PSPACEHard e p := by
  constructor
  · intro hard B input q member
    exact (reduces_iff input e q p).mp
      (hard input.encoding q ((inPSPACE_iff input q).mpr member))
  · intro hard B Γ _ input q member
    let source : FiniteEncoding B := ⟨Γ, inferInstance, input⟩
    exact (reduces_iff source e q p).mpr
      (hard source q ((inPSPACE_iff source q).mp member))

theorem npComplete_iff {A : Type} (e : FiniteEncoding A) (p : A → Prop) :
    ComplexityAbstract.NPComplete e.encode p ↔ Complexity.NPComplete e p :=
  and_congr (inNP_iff e p) (npHard_iff e p)

theorem pspaceComplete_iff {A : Type} (e : FiniteEncoding A) (p : A → Prop) :
    ComplexityAbstract.PSPACEComplete e.encode p ↔ Complexity.PSPACEComplete e p :=
  and_congr (inPSPACE_iff e p) (pspaceHard_iff e p)

/-- Reinterpret a machine across bijective data and symbol representations.
The physical input/output words and step bound are preserved. -/
def recodePolyTime {A B C D Γ Γ' Δ Δ' : Type}
    (input : A → List Γ) (nativeInput : B → List Γ')
    (output : C → List Δ) (nativeOutput : D → List Δ')
    (a : A ≃ B) (b : C ≃ D) (s : Γ ≃ Γ') (t : Δ ≃ Δ')
    (hi : ∀ x, (input x).map s = nativeInput (a x))
    (ho : ∀ y, (output y).map t = nativeOutput (b y))
    {f : B → D} (computer : Turing.TM2ComputableInPolyTime nativeInput nativeOutput f) :
    Turing.TM2ComputableInPolyTime input output (fun x => b.symm (f (a x))) := by
  let inputAlphabet := computer.inputAlphabet.trans s.symm
  let outputAlphabet := computer.outputAlphabet.trans t.symm
  have inWord (x : A) : (input x).map inputAlphabet.invFun =
      (nativeInput (a x)).map computer.inputAlphabet.invFun := by
    rw [← hi x, List.map_map]
    rfl
  have outWord (y : C) : (output y).map outputAlphabet.invFun =
      (nativeOutput (b y)).map computer.outputAlphabet.invFun := by
    rw [← ho y, List.map_map]
    rfl
  refine { tm := computer.tm
           inputAlphabet := inputAlphabet
           outputAlphabet := outputAlphabet
           time := computer.time
           outputsFun := ?_ }
  intro x
  rw [inWord, outWord, b.apply_symm_apply]
  have lengths : (input x).length = (nativeInput (a x)).length := by
    rw [← hi x, List.length_map]
  rw [lengths]
  exact computer.outputsFun (a x)

theorem inNP_recode {A B Γ Δ : Type} (input : A → List Γ) (native : B → List Δ)
    (a : A ≃ B) (s : Γ ≃ Δ) (words : ∀ x, (input x).map s = native (a x))
    (p : A → Prop) (q : B → Prop) (correct : ∀ x, p x ↔ q (a x))
    (member : ComplexityAbstract.InNP native q) : ComplexityAbstract.InNP input p := by
  obtain ⟨verify, ⟨computer⟩, bound, accepted⟩ := member
  have witnesses (x : A × List Bool) :
      (ComplexityAbstract.witnessWord input x).map (Equiv.sumCongr s (Equiv.refl _)) =
        ComplexityAbstract.witnessWord native ((Equiv.prodCongr a (Equiv.refl _)) x) := by
    rcases x with ⟨x, w⟩
    simp [ComplexityAbstract.witnessWord, List.map_map, ← words x, Function.comp_def]
  refine ⟨(fun x w => verify (a x) w), ⟨recodePolyTime _ _ _ _
    (Equiv.prodCongr a (Equiv.refl _)) (Equiv.refl _)
    (Equiv.sumCongr s (Equiv.refl _)) (Equiv.refl _)
    witnesses (fun _ => by simp) computer⟩, bound, ?_⟩
  intro x
  have lengths : (input x).length = (native (a x)).length := by
    rw [← words x, List.length_map]
  rw [lengths, correct]
  exact accepted (a x)

theorem inPSPACE_recode {A B Γ Δ : Type} (input : A → List Γ) (native : B → List Δ)
    (a : A ≃ B) (s : Γ ≃ Δ) (words : ∀ x, (input x).map s = native (a x))
    (p : A → Prop) (q : B → Prop) (correct : ∀ x, p x ↔ q (a x))
    (member : ComplexityAbstract.InPSPACE native q) : ComplexityAbstract.InPSPACE input p := by
  obtain ⟨d⟩ := member
  let inputAlphabet := d.inputAlphabet.trans s.symm
  have inWord (x : A) : (input x).map inputAlphabet.invFun =
      (native (a x)).map d.inputAlphabet.invFun := by
    rw [← words x, List.map_map]
    rfl
  refine ⟨{ tm := d.tm, inputAlphabet := inputAlphabet, outputAlphabet := d.outputAlphabet
            stackAlphabetFinite := d.stackAlphabetFinite
            result := fun x => d.result (a x)
            correct := fun x => (d.correct (a x)).trans (correct x).symm
            outputs := fun x => ?_
            space := d.space
            space_le := fun x cfg reach => ?_ }⟩
  · rw [inWord]
    exact d.outputs (a x)
  · have lengths : (input x).length = (native (a x)).length := by
      rw [← words x, List.length_map]
    rw [lengths]
    rw [inWord] at reach
    exact d.space_le (a x) cfg reach

/-- Re-encoding the target preserves a reduction without running a conversion:
the same output stack is read through the symbol equivalence. -/
theorem reduces_recode_target {A B C Γ Δ Ε : Type}
    (input : A → List Γ) (native : B → List Δ) (source : C → List Ε)
    (a : A ≃ B) (s : Γ ≃ Δ) (words : ∀ x, (input x).map s = native (a x))
    (p : A → Prop) (q : B → Prop) (r : C → Prop)
    (correct : ∀ x, p x ↔ q (a x))
    (reduction : ComplexityAbstract.Reduces source native r q) :
    ComplexityAbstract.Reduces source input r p := by
  obtain ⟨f, ⟨computer⟩, h⟩ := reduction
  refine ⟨(fun x => a.symm (f x)), ⟨recodePolyTime source source input native
    (Equiv.refl _) a (Equiv.refl _) s (fun _ => by simp) words computer⟩, ?_⟩
  intro x
  have hc : p (a.symm (f x)) ↔ q (f x) := by simpa using correct (a.symm (f x))
  exact (h x).trans hc.symm

theorem npHard_recode {A B Γ Δ : Type} (input : A → List Γ) (native : B → List Δ)
    (a : A ≃ B) (s : Γ ≃ Δ) (words : ∀ x, (input x).map s = native (a x))
    (p : A → Prop) (q : B → Prop) (correct : ∀ x, p x ↔ q (a x))
    (hard : ComplexityAbstract.NPHard native q) : ComplexityAbstract.NPHard input p := by
  intro C Ε _ e r member
  exact reduces_recode_target input native e.encode a s words p q r correct (hard e r member)

theorem npComplete_recode {A B Γ Δ : Type} (input : A → List Γ) (native : B → List Δ)
    (a : A ≃ B) (s : Γ ≃ Δ) (words : ∀ x, (input x).map s = native (a x))
    (p : A → Prop) (q : B → Prop) (correct : ∀ x, p x ↔ q (a x))
    (complete : ComplexityAbstract.NPComplete native q) : ComplexityAbstract.NPComplete input p :=
  ⟨inNP_recode input native a s words p q correct complete.1,
    npHard_recode input native a s words p q correct complete.2⟩

theorem pspaceComplete_recode {A B Γ Δ : Type} (input : A → List Γ) (native : B → List Δ)
    (a : A ≃ B) (s : Γ ≃ Δ) (words : ∀ x, (input x).map s = native (a x))
    (p : A → Prop) (q : B → Prop) (correct : ∀ x, p x ↔ q (a x))
    (complete : ComplexityAbstract.PSPACEComplete native q) :
    ComplexityAbstract.PSPACEComplete input p := by
  refine ⟨inPSPACE_recode input native a s words p q correct complete.1, ?_⟩
  intro C Ε _ e r member
  exact reduces_recode_target input native e.encode a s words p q r correct (complete.2 e r member)


/-- Computable bijections preserve co-r.e.-completeness. -/
theorem coRE_recode {A B : Type} [Primcodable A] [Primcodable B]
    (a : A ≃ B) (forward : Computable a) (backward : Computable a.symm)
    (p : A → Prop) (q : B → Prop) (correct : ∀ x, p x ↔ q (a x))
    (complete : LeanWang.CoREComplete q) : LeanWang.CoREComplete p := by
  refine ⟨?_, ?_⟩
  · have equal : p = fun x => q (a x) := funext fun x => propext (correct x)
    rw [equal]
    exact LeanWang.REPred.comp complete.1 forward
  · intro C _ r member
    obtain ⟨f, computable, preserves⟩ := complete.2 r member
    refine ⟨(fun x => a.symm (f x)), backward.comp computable, fun x => ?_⟩
    have hc : p (a.symm (f x)) ↔ q (f x) := by simpa using correct (a.symm (f x))
    exact (preserves x).trans hc.symm

theorem npComplete_congr {A Γ : Type} {encode : A → List Γ} {p q : A → Prop}
    (correct : ∀ x, p x ↔ q x) (complete : ComplexityAbstract.NPComplete encode p) :
    ComplexityAbstract.NPComplete encode q := by
  have equal : p = q := funext fun x => propext (correct x)
  exact equal ▸ complete

theorem pspaceComplete_congr {A Γ : Type} {encode : A → List Γ} {p q : A → Prop}
    (correct : ∀ x, p x ↔ q x) (complete : ComplexityAbstract.PSPACEComplete encode p) :
    ComplexityAbstract.PSPACEComplete encode q := by
  have equal : p = q := funext fun x => propext (correct x)
  exact equal ▸ complete

end LeanTrominoes.ComplexityAbstractBridge
