/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFSplitLiteralCompiler
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileSemantics
import LeanTrominoes.PeriodicCNFFlatEncoding
import LeanTrominoes.PeriodicCNFTransition

/-! # The split literal printer emits the native flat formula fields -/
namespace LeanTrominoes.PeriodicCNF.SplitLiteralPrinter
open UnaryProgramClauseProfile UnaryProgramTokens PeriodicCNFFlatEncoding

/-- One finite profile per literal; the first also carries its clause arity. -/
def clauseMetadata (profiles : List LiteralProfile) : List Metadata :=
  match profiles with
  | [] => []
  | p::ps => (some (Fin.ofNat 4 (ps.length+1)),p) :: ps.map (none,·)

def clauseRecords (clause : PeriodicClause Nat) : List (Metadata × Nat) :=
  match clause with
  | [] => []
  | l::ls => ((some (Fin.ofNat 4 (ls.length+1)),LiteralProfile.ofLiteral l),l.atom) ::
      ls.map (fun l => ((none,LiteralProfile.ofLiteral l),l.atom))

def records (f : PeriodicCNF Nat) : List (Metadata × Nat) := f.clauses.flatMap clauseRecords

theorem records_metadata (f : PeriodicCNF Nat) :
    (records f).map Prod.fst = f.clauses.flatMap (fun c => clauseMetadata (c.map LiteralProfile.ofLiteral)) := by
  simp only [records,List.map_flatMap]
  apply List.flatMap_congr
  intro c _
  cases c <;> simp [clauseRecords,clauseMetadata,List.map_map,Function.comp_def]

theorem records_atoms (f : PeriodicCNF Nat) : (records f).map Prod.snd=f.variableOccurrences := by
  simp only [records,List.map_flatMap,variableOccurrences]
  apply List.flatMap_congr
  intro c _
  cases c <;> simp [clauseRecords,List.map_map,Function.comp_def]

private theorem block_literal (l : PeriodicLiteral Nat) (forward : l.IsForwardLocal) :
    literalBlock (none,LiteralProfile.ofLiteral l) l.atom = CountedUnaryFieldTokens.fields (literalFields l) := by
  rcases l with ⟨atom,offset,value⟩
  rcases forward with h | h <;> change offset=_ at h <;> subst offset <;> cases value <;> rfl

private theorem body_literals (ls : List (PeriodicLiteral Nat))
    (forward : ∀ l∈ls, l.IsForwardLocal) :
    (ls.map (fun l => ((none,LiteralProfile.ofLiteral l),l.atom))).flatMap
      (fun p => literalBlock p.1 p.2) = CountedUnaryFieldTokens.fields (ls.flatMap literalFields) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.map_cons,List.flatMap_cons]
    rw [block_literal l (forward l (by simp)),ih (fun l hl => forward l (by simp [hl]))]
    simp [CountedUnaryFieldTokens.fields,List.flatMap_append]

theorem clauseRecords_tokens (c : PeriodicClause Nat) (nonempty : c≠[])
    (width : c.length≤3) (forward : ∀ l∈c, l.IsForwardLocal) :
    (clauseRecords c).flatMap (fun p => literalBlock p.1 p.2) =
      CountedUnaryFieldTokens.countedFieldBlock (clauseFields c) := by
  cases c with
  | nil => contradiction
  | cons l ls =>
    have arity : (Fin.ofNat 4 (ls.length+1)).val=ls.length+1 := by
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by simpa only [List.length_cons] using Nat.lt_succ_of_le width)
    change (ls.length+1)%4=ls.length+1 at arity
    have body := body_literals ls (fun l hl => forward l (by simp [hl]))
    have first := block_literal l (forward l (by simp))
    simp only [clauseRecords,List.flatMap_cons]
    rw [body]
    have split (m : Metadata) (atom : Nat) : literalBlock m atom =
        header m ++ literalBlock (none,m.2) atom := by
      simp [literalBlock,header,suffix,List.append_assoc]
    rw [split]
    rw [first]
    simp [header,arity,CountedUnaryFieldTokens.countedFieldBlock,clauseFields,
      CountedUnaryFieldTokens.fields,List.flatMap_append,List.append_assoc]

theorem records_tokens (f : PeriodicCNF Nat) (nonempty : ∀ c∈f.clauses,c≠[])
    (width : f.WidthAtMost 3) (forward : f.IsForwardLocal) :
    (records f).flatMap (fun p => literalBlock p.1 p.2) =
      CountedUnaryFieldTokens.countedFieldBlocks (f.clauses.map clauseFields) := by
  simp only [records,List.flatMap_assoc,CountedUnaryFieldTokens.countedFieldBlocks,List.flatMap_map]
  apply List.flatMap_congr
  intro c hc
  exact clauseRecords_tokens c (nonempty c hc) (width c hc) (forward c hc)

theorem finalize_records (f : PeriodicCNF Nat) (nonempty : ∀ c∈f.clauses,c≠[])
    (width : f.WidthAtMost 3) (forward : f.IsForwardLocal) :
    UnaryProgramTokenFinalizer.countAndFinalize
      ((records f).flatMap (fun p => literalBlock p.1 p.2)) =
      UnaryFieldEncoderMachine.unaryFields (formulaFields f) := by
  rw [records_tokens f nonempty width forward]
  simpa [CountedUnaryFieldTokens.fields,formulaFields,List.flatMap_def] using
    CountedUnaryFieldTokens.countAndFinalize_fields_countedFieldBlocks [] (f.clauses.map clauseFields)

end LeanTrominoes.PeriodicCNF.SplitLiteralPrinter
