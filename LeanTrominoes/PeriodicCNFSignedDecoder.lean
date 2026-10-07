/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFiniteConsequencesComputability

/-! # Signed local decoders preserve finite prescriptions

Each source bit is read from one target bit at a fixed relative offset,
possibly complemented. Global soundness of such a decoder supplies a finite
window sufficient to recover each source clause.
-/
namespace LeanTrominoes.PeriodicCNF.SignedDecoder
variable {V W : Type}

abbrev Read (V W : Type) := V → PeriodicLiteral W

def decode (read : Read V W) (a : W → Cell → Bool) : V → Cell → Bool :=
  fun v c => if (read v).value then a (read v).atom (Cell.add c (read v).offset)
    else !(a (read v).atom (Cell.add c (read v).offset))

def transportPin (read : Read V W) (pin : (V × Cell) × Bool) : (W × Cell) × Bool :=
  (((read pin.1.1).atom,Cell.add pin.1.2 (read pin.1.1).offset),
    if (read pin.1.1).value then pin.2 else !pin.2)

def transportSeed (read : Read V W) (seed : Seed V) : Seed W :=
  seed.map (transportPin read)

def transportLiteral (read : Read V W) (l : PeriodicLiteral V) : PeriodicLiteral W :=
  ⟨(read l.atom).atom,Cell.add l.offset (read l.atom).offset,
    if (read l.atom).value then l.value else !l.value⟩

def transportClause (read : Read V W) (clause : PeriodicClause V) : PeriodicClause W :=
  clause.map (transportLiteral read)

theorem pin_correct (read : Read V W) (a : W → Cell → Bool) (pin : (V × Cell) × Bool) :
    a (transportPin read pin).1.1 (transportPin read pin).1.2 = (transportPin read pin).2 ↔
      decode read a pin.1.1 pin.1.2 = pin.2 := by
  simp only [transportPin,decode]
  cases (read pin.1.1).value <;>
    cases a (read pin.1.1).atom (Cell.add pin.1.2 (read pin.1.1).offset) <;>
    cases pin.2 <;> decide

theorem literal_correct (read : Read V W) (a : W → Cell → Bool)
    (c : Cell) (l : PeriodicLiteral V) :
    (transportLiteral read l).Holds a c ↔ l.Holds (decode read a) c := by
  simp only [PeriodicLiteral.Holds,transportLiteral,decode]
  have assoc : Cell.add c (Cell.add l.offset (read l.atom).offset) =
      Cell.add (Cell.add c l.offset) (read l.atom).offset := by
    ext <;> simp [Cell.add,add_assoc]
  rw [assoc]
  cases (read l.atom).value <;>
    cases a (read l.atom).atom (Cell.add (Cell.add c l.offset) (read l.atom).offset) <;>
    cases l.value <;> decide

theorem clause_correct (read : Read V W) (a : W → Cell → Bool)
    (c : Cell) (clause : PeriodicClause V) :
    (transportClause read clause).Holds a c ↔ clause.Holds (decode read a) c := by
  simp only [PeriodicClause.Holds,transportClause,List.mem_map,exists_exists_and_eq_and,
    literal_correct]

def SupportedSeed (support : Set V) (seed : Seed V) : Prop :=
  ∀ pin ∈ seed, pin.1.1 ∈ support

structure Factor (source : PeriodicCNF V) (target : PeriodicCNF W)
    (read : Read V W) (support : Set V) : Prop where
  sound : ∀ a, target.Satisfies a → source.Satisfies (decode read a)
  complete : ∀ a, source.Satisfies a → ∃ b, target.Satisfies b ∧
    ∀ v ∈ support, ∀ c, decode read b v c = a v c

theorem Factor.seeded_iff {source : PeriodicCNF V} {target : PeriodicCNF W}
    {read : Read V W} {support : Set V} (factor : Factor source target read support)
    (seed : Seed V) (supported : SupportedSeed support seed) :
    source.Seeded seed ↔ target.Seeded (transportSeed read seed) := by
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

def groundClause (read : Read V W) (clause : PeriodicClause V) :
    FiniteConsequences.Clause W :=
  (transportClause read clause).map fun l => ((l.atom,l.offset),l.value)

theorem groundClause_correct (read : Read V W) (a : W → Cell → Bool)
    (clause : PeriodicClause V) :
    FiniteConsequences.Holds (groundClause read clause) a ↔
      clause.Holds (decode read a) (0,0) := by
  rw [← clause_correct]
  simp only [FiniteConsequences.Holds,groundClause,PeriodicClause.Holds,
    PeriodicLiteral.Holds,List.mem_map,exists_exists_and_eq_and]
  simp only [Cell.add,zero_add,Prod.eta]

theorem finite_radius [DecidableEq W] {source : PeriodicCNF V} {target : PeriodicCNF W}
    {read : Read V W} (sound : ∀ a, target.Satisfies a → source.Satisfies (decode read a))
    (clause : PeriodicClause V) (member : clause ∈ source.clauses) :
    ∃ r, FiniteConsequences.FiniteEntails target (groundClause read clause) r := by
  apply (FiniteConsequences.entails_iff _ _).1
  intro a ha
  apply (groundClause_correct _ _ _).2
  exact sound a ha (0,0) clause member

theorem local_clause [DecidableEq W] {target : PeriodicCNF W} {read : Read V W}
    {clause : PeriodicClause V} {r : Nat}
    (forced : FiniteConsequences.FiniteEntails target (groundClause read clause) r)
    (a : W → Cell → Bool) (translate : Cell)
    (patch : ∀ c ∈ TrominoAssignment.boxCellList r,
      ∀ targetClause ∈ target.clauses, targetClause.Holds a (Cell.add translate c)) :
    clause.Holds (decode read a) translate := by
  let shifted : W → Cell → Bool := fun v c => a v (Cell.add translate c)
  have shiftedPatch : ∀ c ∈ TrominoAssignment.boxCellList r,
      ∀ targetClause ∈ target.clauses, targetClause.Holds shifted c := by
    intro c hc cl hcl
    obtain ⟨l,hl,value⟩ := patch c hc cl hcl
    refine ⟨l,hl,?_⟩
    simpa only [PeriodicLiteral.Holds,shifted,Cell.add,add_assoc] using value
  have result := (groundClause_correct read shifted clause).1
    (FiniteConsequences.finiteEntails_sound forced shifted shiftedPatch)
  simpa only [PeriodicClause.Holds,PeriodicLiteral.Holds,decode,shifted,Cell.add,
    zero_add,add_assoc] using result

end LeanTrominoes.PeriodicCNF.SignedDecoder
