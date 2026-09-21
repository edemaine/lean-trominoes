/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceFieldRanks

/-! # Clause and literal indices in the address stream -/
namespace LeanTrominoes.PeriodicCNF.FlatScanner
open PeriodicCNFFlatEncoding

theorem clauseEntries_values (start : Nat) (cs : List (PeriodicClause Nat)) :
    (clauseEntries start cs).map Prod.snd = cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih => simp [clauseEntries,ih]

theorem clauseEntries_length (start : Nat) (cs : List (PeriodicClause Nat)) :
    (clauseEntries start cs).length = cs.length := by
  have h := congrArg List.length (clauseEntries_values start cs)
  simpa using h

theorem clauseEntries_value (start : Nat) (cs : List (PeriodicClause Nat))
    (i : Nat) (hi : i<cs.length) :
    ((clauseEntries start cs)[i]'(by rwa [clauseEntries_length])).2 = cs[i] := by
  have h := congrArg (fun l : List (PeriodicClause Nat) => l[i]?) (clauseEntries_values start cs)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (show i<(clauseEntries start cs).length by rwa [clauseEntries_length]),
    Option.map_some,Option.some.injEq] using h

theorem literalEntries_length (start : Nat) (ls : List (PeriodicLiteral Nat)) :
    (literalEntries start ls).length = ls.length := by
  induction ls generalizing start with
  | nil => rfl
  | cons l ls ih => simp [literalEntries,ih]

theorem literalEntries_get (start : Nat) (ls : List (PeriodicLiteral Nat))
    (i : Nat) (hi : i<ls.length) :
    (literalEntries start ls)[i]'(by rwa [literalEntries_length]) = (start+4*i,ls[i]) := by
  induction ls generalizing start i with
  | nil => simp at hi
  | cons l ls ih =>
    cases i with
    | zero => simp [literalEntries]
    | succ i =>
      simp only [literalEntries,List.getElem_cons_succ]
      rw [ih (start+4) i (by simpa using hi)]
      congr 1
      omega

end LeanTrominoes.PeriodicCNF.FlatScanner

namespace LeanTrominoes.PeriodicCNF.IncidenceFields
open FlatScanner BoundedArithmetic

theorem clause_rank (f : PeriodicCNF Nat) (i : Nat) (hi : i<f.clauses.length) :
    Count.count clauseMarkExpr (FieldSavitch.suffix f)
      ((clauseEntries 1 f.clauses)[i]'(by rwa [clauseEntries_length])).1 = i := by
  rw [clause_rank_count]
  exact SortedAddressRank.before_get_length _ (clauseEntries_sorted _ _) i (by rwa [clauseEntries_length])

theorem literal_rank (f : PeriodicCNF Nat) (i : Nat) (hi : i<(allLiteralEntries 1 f.clauses).length) :
    Count.count literalMarkExpr (FieldSavitch.suffix f) ((allLiteralEntries 1 f.clauses)[i]).1 = i := by
  rw [literal_rank_count]
  exact SortedAddressRank.before_get_length _ (allLiteralEntries_sorted _ _) i hi

end LeanTrominoes.PeriodicCNF.IncidenceFields
