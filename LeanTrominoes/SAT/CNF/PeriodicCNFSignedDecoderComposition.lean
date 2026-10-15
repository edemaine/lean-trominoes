/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSignedDecoder

/-! # Composition and computability of finite-pin decoders -/
namespace LeanTrominoes.PeriodicCNF.SignedDecoder
variable {U V W : Type}

def compose (first : Read U V) (second : Read V W) : Read U W :=
  fun v =>
    let a := first v
    let b := second a.atom
    ⟨b.atom,Cell.add a.offset b.offset,if a.value then b.value else !b.value⟩

theorem decode_compose (first : Read U V) (second : Read V W) (a : W → Cell → Bool) :
    decode (compose first second) a = decode first (decode second a) := by
  funext v c
  simp only [decode,compose]
  have assoc : Cell.add c (Cell.add (first v).offset (second (first v).atom).offset) =
      Cell.add (Cell.add c (first v).offset) (second (first v).atom).offset := by
    ext <;> simp [Cell.add,add_assoc]
  rw [assoc]
  cases (first v).value <;> cases (second (first v).atom).value <;> simp

theorem transportSeed_compose (first : Read U V) (second : Read V W) (seed : Seed U) :
    transportSeed (compose first second) seed =
      transportSeed second (transportSeed first seed) := by
  simp only [transportSeed,List.map_map]
  apply List.map_congr_left
  intro pin _
  simp only [transportPin,compose,Function.comp_def]
  have assoc : Cell.add pin.1.2 (Cell.add (first pin.1.1).offset
      (second (first pin.1.1).atom).offset) =
      Cell.add (Cell.add pin.1.2 (first pin.1.1).offset)
        (second (first pin.1.1).atom).offset := by
    ext <;> simp [Cell.add,add_assoc]
  rw [assoc]
  have boolean (a b c : Bool) :
      (if (if a then b else !b) then c else !c) =
        (if b then (if a then c else !c) else !(if a then c else !c)) := by
    cases a <;> cases b <;> cases c <;> rfl
  exact congrArg (fun value =>
    (((second (first pin.1.1).atom).atom,
      Cell.add (Cell.add pin.1.2 (first pin.1.1).offset)
        (second (first pin.1.1).atom).offset),value))
    (boolean (first pin.1.1).value (second (first pin.1.1).atom).value pin.2)

theorem Factor.compose {source : PeriodicCNF U} {middle : PeriodicCNF V}
    {target : PeriodicCNF W} {first : Read U V} {second : Read V W}
    {sourceSupport : Set U} {middleSupport : Set V}
    (one : Factor source middle first sourceSupport)
    (two : Factor middle target second middleSupport)
    (supported : ∀ v ∈ sourceSupport, (first v).atom ∈ middleSupport) :
    Factor source target (compose first second) sourceSupport := by
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

theorem transportSeed_primrec [Primcodable V] [Primcodable W]
    {read : Read V W} (readComputable : Primrec read) : Primrec (transportSeed read) := by
  have atom : Primrec (fun v : V => (read v).atom) :=
    Primrec.fst.comp (PeriodicLiteral.equivData_primrec.comp readComputable)
  have offset : Primrec (fun v : V => (read v).offset) :=
    Primrec.fst.comp (Primrec.snd.comp (PeriodicLiteral.equivData_primrec.comp readComputable))
  have value : Primrec (fun v : V => (read v).value) :=
    Primrec.snd.comp (Primrec.snd.comp (PeriodicLiteral.equivData_primrec.comp readComputable))
  have pin : Primrec (transportPin read) :=
    Primrec.pair
      (Primrec.pair (atom.comp (Primrec.fst.comp Primrec.fst))
        (Computability.cell_add_primrec.comp (Primrec.snd.comp Primrec.fst)
          (offset.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.ite (Primrec.eq.comp (value.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const true))
        Primrec.snd (Primrec.not.comp Primrec.snd))
  exact Primrec.list_map Primrec.id (pin.comp Primrec.snd)

open Lean Elab Command in
run_cmd do
  for name in [``Factor.compose,``transportSeed_primrec,``local_clause] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicCNF.SignedDecoder
