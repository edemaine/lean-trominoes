/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSignedDecoderComposition

/-! # Finite prescriptions across different Boolean constraint systems -/
namespace LeanTrominoes.PeriodicCNF.SignedDecoder
variable {U V W : Type}

def Prescribed (valid : (V → Cell → Bool) → Prop) (seed : Seed V) : Prop :=
  ∃ a, valid a ∧ ∀ pin ∈ seed, a pin.1.1 pin.1.2 = pin.2

structure LogicalFactor (source : (V → Cell → Bool) → Prop)
    (target : (W → Cell → Bool) → Prop) (read : Read V W) (support : Set V) : Prop where
  sound : ∀ a, target a → source (decode read a)
  complete : ∀ a, source a → ∃ b, target b ∧
    ∀ v ∈ support, ∀ c, decode read b v c = a v c

theorem Factor.logical {source : PeriodicCNF V} {target : PeriodicCNF W}
    {read : Read V W} {support : Set V} (factor : Factor source target read support) :
    LogicalFactor source.Satisfies target.Satisfies read support :=
  ⟨factor.sound,factor.complete⟩

theorem LogicalFactor.cnf {source : PeriodicCNF V} {target : PeriodicCNF W}
    {read : Read V W} {support : Set V}
    (factor : LogicalFactor source.Satisfies target.Satisfies read support) :
    Factor source target read support := ⟨factor.sound,factor.complete⟩

theorem LogicalFactor.seeded_iff {source : (V → Cell → Bool) → Prop}
    {target : (W → Cell → Bool) → Prop} {read : Read V W} {support : Set V}
    (factor : LogicalFactor source target read support) (seed : Seed V)
    (supported : SupportedSeed support seed) :
    Prescribed source seed ↔ Prescribed target (transportSeed read seed) := by
  constructor
  · rintro ⟨a,ha,pins⟩
    obtain ⟨b,hb,inverse⟩ := factor.complete a ha
    refine ⟨b,hb,?_⟩
    intro pin member
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp member
    apply (pin_correct _ _ _).2
    rw [inverse p.1.1 (supported p hp) p.1.2]
    exact pins p hp
  · rintro ⟨a,ha,pins⟩
    refine ⟨decode read a,factor.sound a ha,?_⟩
    intro pin member
    apply (pin_correct _ _ _).1
    exact pins _ (List.mem_map.mpr ⟨pin,member,rfl⟩)

theorem LogicalFactor.compose {source : (U → Cell → Bool) → Prop}
    {middle : (V → Cell → Bool) → Prop} {target : (W → Cell → Bool) → Prop}
    {first : Read U V} {second : Read V W} {sourceSupport : Set U} {middleSupport : Set V}
    (one : LogicalFactor source middle first sourceSupport)
    (two : LogicalFactor middle target second middleSupport)
    (supported : ∀ v ∈ sourceSupport, (first v).atom ∈ middleSupport) :
    LogicalFactor source target (compose first second) sourceSupport := by
  constructor
  · intro a ha
    rw [decode_compose]
    exact one.sound _ (two.sound a ha)
  · intro a ha
    obtain ⟨b,hb,firstInverse⟩ := one.complete a ha
    obtain ⟨c,hc,secondInverse⟩ := two.complete b hb
    refine ⟨c,hc,?_⟩
    intro v hv location
    rw [decode_compose]
    have equal : decode first (decode second c) v location = decode first b v location := by
      change (if (first v).value then
        decode second c (first v).atom (Cell.add location (first v).offset)
        else !(decode second c (first v).atom (Cell.add location (first v).offset))) =
        (if (first v).value then b (first v).atom (Cell.add location (first v).offset)
        else !(b (first v).atom (Cell.add location (first v).offset)))
      rw [secondInverse (first v).atom (supported v hv) (Cell.add location (first v).offset)]
    exact equal.trans (firstInverse v hv location)

theorem LogicalFactor.congrTarget {source : (V → Cell → Bool) → Prop}
    {target other : (W → Cell → Bool) → Prop} {read : Read V W} {support : Set V}
    (factor : LogicalFactor source target read support) (same : ∀ a, target a ↔ other a) :
    LogicalFactor source other read support := by
  constructor
  · intro a ha
    exact factor.sound a ((same a).2 ha)
  · intro a ha
    obtain ⟨b,hb,inverse⟩ := factor.complete a ha
    exact ⟨b,(same b).1 hb,inverse⟩

end LeanTrominoes.PeriodicCNF.SignedDecoder
