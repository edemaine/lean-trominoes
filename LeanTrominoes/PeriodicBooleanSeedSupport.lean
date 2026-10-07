/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicBooleanSignedDecoder
import LeanTrominoes.PeriodicCNFSeededCoRE

/-! # Effective removal of prescriptions on unused Boolean variables -/
namespace LeanTrominoes.PeriodicCNF.SignedDecoder
variable {V W : Type} [DecidableEq V]

def Consistent (seed : Seed V) : Prop := FiniteSearch.Check (seed.map (fun pin => [pin]))
instance (seed : Seed V) : Decidable (Consistent seed) := by unfold Consistent; infer_instance

theorem consistent_iff (seed : Seed V) :
    Consistent seed ↔ ∃ a : V → Cell → Bool, ∀ pin ∈ seed, a pin.1.1 pin.1.2 = pin.2 := by
  rw [Consistent,FiniteSearch.check_iff]
  simp only [FiniteSearch.Holds,List.forall_mem_map,List.mem_singleton,exists_eq_left]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨fun v c => a (v,c),ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨fun p => a p.1 p.2,ha⟩

def supportedPart (support : List V) (seed : Seed V) : Seed V :=
  seed.filter (fun pin => pin.1.1 ∈ support)

theorem prescribed_support_iff (valid : (V → Cell → Bool) → Prop) (support : List V)
    (stable : ∀ a b, (∀ v ∈ support, ∀ c, a v c = b v c) → (valid a ↔ valid b))
    (seed : Seed V) :
    Prescribed valid seed ↔ Consistent seed ∧ Prescribed valid (supportedPart support seed) := by
  constructor
  · rintro ⟨a,ha,pins⟩
    exact ⟨(consistent_iff seed).2 ⟨a,pins⟩,a,ha,
      fun pin member => pins pin (List.mem_filter.mp member).1⟩
  · rintro ⟨consistent,a,ha,pins⟩
    obtain ⟨b,hb⟩ := (consistent_iff seed).1 consistent
    let combined : V → Cell → Bool := fun v c => if v ∈ support then a v c else b v c
    refine ⟨combined,(stable a combined (fun v hv c => by simp [combined,hv])).1 ha,?_⟩
    intro pin member
    by_cases used : pin.1.1 ∈ support
    · simpa [combined,used] using pins pin (List.mem_filter.mpr ⟨member,by simpa using used⟩)
    · simpa [combined,used] using hb pin member

def conflictingSeed (v : W) : Seed W := [((v,(0,0)),true),((v,(0,0)),false)]

theorem conflictingSeed_impossible (valid : (W → Cell → Bool) → Prop) (v : W) :
    ¬ Prescribed valid (conflictingSeed v) := by
  rintro ⟨a,_,pins⟩
  have one := pins ((v,(0,0)),true) (by simp [conflictingSeed])
  have two := pins ((v,(0,0)),false) (by simp [conflictingSeed])
  rw [one] at two
  contradiction

def supportedReduction (support : List V) (read : Read V W) (fallback : W) (seed : Seed V) : Seed W :=
  if Consistent seed then transportSeed read (supportedPart support seed) else conflictingSeed fallback

theorem supportedReduction_correct {source : (V → Cell → Bool) → Prop}
    {target : (W → Cell → Bool) → Prop} {read : Read V W} (support : List V) (fallback : W)
    (factor : LogicalFactor source target read {v | v ∈ support})
    (stable : ∀ a b, (∀ v ∈ support, ∀ c, a v c = b v c) → (source a ↔ source b))
    (seed : Seed V) :
    Prescribed source seed ↔ Prescribed target (supportedReduction support read fallback seed) := by
  rw [prescribed_support_iff source support stable seed]
  by_cases consistent : Consistent seed
  · simp only [supportedReduction,consistent,ite_true,true_and]
    exact factor.seeded_iff _ (fun pin member => by
      exact of_decide_eq_true (List.mem_filter.mp member).2)
  · simp only [consistent,false_and,supportedReduction,ite_false]
    exact (iff_false_intro (conflictingSeed_impossible target fallback)).symm

theorem consistent_primrec [Primcodable V] : PrimrecPred (@Consistent V _) :=
  FiniteSearch.check_primrec.comp
    (Primrec.list_map Primrec.id (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

theorem supportedPart_primrec [Primcodable V] (support : List V) : Primrec (supportedPart support) :=
  Primrec.listFilter
    (FiniteSearch.mem_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.const support))

theorem supportedReduction_primrec [Primcodable V] [Primcodable W]
    (support : List V) {read : Read V W} (computed : Primrec read) (fallback : W) :
    Primrec (supportedReduction support read fallback) :=
  Primrec.ite consistent_primrec
    ((transportSeed_primrec computed).comp (supportedPart_primrec support))
    (Primrec.const (conflictingSeed fallback))

end LeanTrominoes.PeriodicCNF.SignedDecoder
