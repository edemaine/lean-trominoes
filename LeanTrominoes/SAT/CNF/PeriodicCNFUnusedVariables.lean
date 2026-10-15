/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSignedDecoderComposition

/-! # Adding unconstrained variables to a periodic formula -/
namespace LeanTrominoes.PeriodicCNF.UnusedVariables
open SignedDecoder
variable {V W U : Type}

def literal (l : PeriodicLiteral V) : PeriodicLiteral (V ⊕ U) :=
  ⟨Sum.inl l.atom,l.offset,l.value⟩

def clause (c : PeriodicClause V) : PeriodicClause (V ⊕ U) := c.map literal

def formula (f : PeriodicCNF V) : PeriodicCNF (V ⊕ U) := ⟨f.clauses.map clause⟩

def restrict (a : (V ⊕ U) → Cell → Bool) : V → Cell → Bool := fun v => a (.inl v)

theorem clause_holds (c : PeriodicClause V) (a : (V ⊕ U) → Cell → Bool) (p : Cell) :
    (clause c).Holds a p ↔ c.Holds (restrict a) p := by
  simp only [clause,PeriodicClause.Holds,List.mem_map,exists_exists_and_eq_and]
  rfl

theorem satisfies_iff (f : PeriodicCNF V) (a : (V ⊕ U) → Cell → Bool) :
    (formula f).Satisfies a ↔ f.Satisfies (restrict a) := by
  constructor
  · intro valid p c member
    exact (clause_holds c a p).1 (valid p (clause c) (List.mem_map.mpr ⟨c,member,rfl⟩))
  · intro valid p c member
    change c ∈ f.clauses.map clause at member
    obtain ⟨base,baseMember,rfl⟩ := List.mem_map.mp member
    exact (clause_holds base a p).2 (valid p base baseMember)

def read (r : Read W V) : Read W (V ⊕ U) := fun v => literal (r v)

theorem decode_read (r : Read W V) (a : (V ⊕ U) → Cell → Bool) :
    decode (read r) a = decode r (restrict a) := rfl

theorem read_primrec [Primcodable V] [Primcodable W] [Primcodable U]
    {r : Read W V} (computable : Primrec r) : Primrec (read (U := U) r) := by
  have data := PeriodicLiteral.equivData_primrec.comp computable
  exact PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.sumInl.comp (Primrec.fst.comp data)) (Primrec.snd.comp data))

end LeanTrominoes.PeriodicCNF.UnusedVariables
