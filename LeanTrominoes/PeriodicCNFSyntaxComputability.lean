/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFCoRE

/-! # Effective locality, width, and occurrence bounds -/
namespace LeanTrominoes.PeriodicCNF
open Computability
variable {V : Type} [Primcodable V]

theorem isLocal_primrec : PrimrecPred (@IsLocal V) := by
  have offset : Primrec (fun l : PeriodicLiteral V => l.offset) :=
    Primrec.fst.comp (Primrec.snd.comp PeriodicLiteral.equivData_primrec)
  have abs : Primrec Int.natAbs :=
    (intCodeMagnitude_primrec.comp Primrec.encode).of_eq intCodeMagnitude_encode
  have dx : Primrec₂ fun (a b : PeriodicLiteral V) => (a.offset.1 - b.offset.1).natAbs :=
    abs.comp (int_subtract_primrec.comp
      (Primrec.fst.comp (offset.comp Primrec.fst))
      (Primrec.fst.comp (offset.comp Primrec.snd)))
  have dy : Primrec₂ fun (a b : PeriodicLiteral V) => (a.offset.2 - b.offset.2).natAbs :=
    abs.comp (int_subtract_primrec.comp
      (Primrec.snd.comp (offset.comp Primrec.fst))
      (Primrec.snd.comp (offset.comp Primrec.snd)))
  have near : PrimrecRel fun (a b : PeriodicLiteral V) =>
      PeriodicClause.offsetDistance a b ≤ 1 :=
    Primrec.nat_le.comp (Primrec.nat_add.comp dx dy) (Primrec.const 1)
  have row : PrimrecRel fun (a : PeriodicLiteral V) (c : PeriodicClause V) =>
      ∀ b ∈ c, PeriodicClause.offsetDistance a b ≤ 1 := near.swap.forall_mem_list.swap
  have clause : PrimrecPred (@PeriodicClause.IsLocal V) :=
    row.forall_mem_list.comp Primrec.id Primrec.id
  exact clause.forall_mem_list.comp PeriodicCNF.equivData_primrec

theorem widthAtMost_primrec (k : Nat) : PrimrecPred (@WidthAtMost V k) :=
  (Primrec.nat_le.comp Primrec.list_length (Primrec.const k)).forall_mem_list.comp
    PeriodicCNF.equivData_primrec

private theorem variableOccurrences_primrec : Primrec (@variableOccurrences V) :=
  Primrec.list_flatMap PeriodicCNF.equivData_primrec
    (Primrec.list_map Primrec.snd
      (Primrec.fst.comp (PeriodicLiteral.equivData_primrec.comp Primrec.snd)))

variable [BEq V] [LawfulBEq V]

private theorem count_primrec : Primrec₂ fun (a : V) (xs : List V) => xs.count a := by
  classical
  have step : Primrec₂ fun (p : V × List V) (q : V × Nat) =>
      if q.1 = p.1 then q.2 + 1 else q.2 :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr Primrec.snd (Primrec.const 0) step).of_eq
  intro p
  induction p.2 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, List.count_cons]
    rw [ih]
    split <;> simp_all

theorem occurrencesAtMost_primrec (k : Nat) : PrimrecPred (@OccurrencesAtMost V _ _ k) := by
  have countBound : PrimrecRel fun (a : V) (f : PeriodicCNF V) =>
      (variableOccurrences f).count a ≤ k :=
    Primrec.nat_le.comp
      (count_primrec.comp Primrec.fst (variableOccurrences_primrec.comp Primrec.snd))
      (Primrec.const k)
  apply (countBound.forall_mem_list.comp variableOccurrences_primrec Primrec.id).of_eq
  intro f
  constructor
  · intro h a
    by_cases ha : a ∈ variableOccurrences f
    · exact h a ha
    · simp [List.count_eq_zero.mpr ha]
  · intro h a _; exact h a

end LeanTrominoes.PeriodicCNF
