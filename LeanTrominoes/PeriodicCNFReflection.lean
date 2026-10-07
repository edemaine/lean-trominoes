/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFSeededCoRE

/-! # Vertical reflection preserves periodic formulas and finite prescriptions -/
namespace LeanTrominoes.PeriodicCNF.Reflection
variable {V : Type}

def cell (c : Cell) : Cell := (c.1,-c.2)
@[simp] theorem cell_cell (c : Cell) : cell (cell c) = c := by ext <;> simp [cell]
theorem cell_add (a b : Cell) : cell (Cell.add a b) = Cell.add (cell a) (cell b) := by
  ext <;> simp [cell,Cell.add,add_comm]

def literal (l : PeriodicLiteral V) : PeriodicLiteral V := ⟨l.atom,cell l.offset,l.value⟩
def formula (f : PeriodicCNF V) : PeriodicCNF V := ⟨f.clauses.map (List.map literal)⟩
def assignment (a : V → Cell → Bool) : V → Cell → Bool := fun v c => a v (cell c)
def seed (s : PeriodicCNF.Seed V) : PeriodicCNF.Seed V := s.map fun p => ((p.1.1,cell p.1.2),p.2)

theorem literal_holds (a : V → Cell → Bool) (c : Cell) (l : PeriodicLiteral V) :
    (literal l).Holds a c ↔ l.Holds (assignment a) (cell c) := by
  simp [PeriodicLiteral.Holds,literal,assignment,cell_add]

theorem satisfies_iff (f : PeriodicCNF V) (a : V → Cell → Bool) :
    (formula f).Satisfies a ↔ f.Satisfies (assignment a) := by
  have clause (ls : PeriodicClause V) (c : Cell) :
      PeriodicClause.Holds a c (ls.map literal) ↔ ls.Holds (assignment a) (cell c) := by
    simp [PeriodicClause.Holds,literal_holds]
  constructor
  · intro ha c ls member
    have holds := (clause ls (cell c)).1 (ha (cell c) _ (List.mem_map.mpr ⟨ls,member,rfl⟩))
    simpa using holds
  · intro ha c ls member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact (clause original c).2 (ha _ original originalMember)

@[simp] theorem assignment_assignment (a : V → Cell → Bool) : assignment (assignment a) = a := by
  funext v c
  simp [assignment]

theorem seeded_iff (f : PeriodicCNF V) (s : PeriodicCNF.Seed V) :
    (formula f).Seeded (seed s) ↔ f.Seeded s := by
  constructor
  · rintro ⟨a,ha,pins⟩
    refine ⟨assignment a,(satisfies_iff f a).1 ha,?_⟩
    intro pin member
    exact pins _ (List.mem_map.mpr ⟨pin,member,rfl⟩)
  · rintro ⟨a,ha,pins⟩
    refine ⟨assignment a,(satisfies_iff f _).2 (by simpa using ha),?_⟩
    intro pin member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    simpa [assignment] using pins original originalMember

theorem cell_primrec : Primrec cell :=
  Primrec.pair Primrec.fst (Computability.int_negate_primrec.comp Primrec.snd)

theorem seed_primrec [Primcodable V] : Primrec (@seed V) :=
  Primrec.list_map Primrec.id
    (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (cell_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd))

end LeanTrominoes.PeriodicCNF.Reflection
