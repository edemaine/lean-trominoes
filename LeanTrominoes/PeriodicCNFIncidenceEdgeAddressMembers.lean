/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceEdgeAddresses

/-! # Addressed incidence edges are precisely the clause/literal loops -/
namespace LeanTrominoes.PeriodicCNF.IncidenceFields
open FlatScanner BoundedArithmetic

theorem clause_tag_rank (f : PeriodicCNF Nat) (entry : Nat × PeriodicClause Nat) (i : Nat)
    (hm : (entry,i)∈(clauseEntries 1 f.clauses).zipIdx) :
    Count.count clauseMarkExpr (FieldSavitch.suffix f) entry.1 = i := by
  have info := List.mem_zipIdx hm
  have bound : i<(clauseEntries 1 f.clauses).length := by simpa using info.2.1
  have value : entry=(clauseEntries 1 f.clauses)[i] := by simpa using info.2.2
  rw [value]
  exact clause_rank f i (by rwa [clauseEntries_length] at bound)

theorem clause_tagged_member (f : PeriodicCNF Nat) (h : Nat) (c : PeriodicClause Nat)
    (hc : (h,c)∈clauseEntries 1 f.clauses) :
    ((h,c),Count.count clauseMarkExpr (FieldSavitch.suffix f) h)∈(clauseEntries 1 f.clauses).zipIdx := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hc
  have tagged : ((h,c),i)∈(clauseEntries 1 f.clauses).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem hi,eq]
  rwa [clause_tag_rank f (h,c) i tagged]

theorem literalEntries_mem_iff (start : Nat) (ls : List (PeriodicLiteral Nat)) (p : Nat) (l : PeriodicLiteral Nat) :
    (p,l)∈literalEntries start ls ↔ ∃ k, ∃ hk : k<ls.length, p=start+4*k ∧ l=ls[k] := by
  constructor
  · intro member
    obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp member
    have bound : k<ls.length := by rwa [literalEntries_length] at hk
    rw [literalEntries_get start ls k bound] at eq
    exact ⟨k,bound,(congrArg Prod.fst eq).symm,(congrArg Prod.snd eq).symm⟩
  · rintro ⟨k,hk,rfl,rfl⟩
    rw [← literalEntries_get start ls k hk]
    exact List.getElem_mem _

theorem edgeEntries_mem_iff (f : PeriodicCNF Nat) (entry : Nat × PeriodicEdge (CNFVertex Nat)) :
    entry∈edgeEntries 1 0 f.clauses ↔
      ∃ h c, (h,c)∈clauseEntries 1 f.clauses ∧ ∃ k, ∃ hk : k<c.length,
        entry=(h+1+4*k,incidenceEdge (Count.count clauseMarkExpr (FieldSavitch.suffix f) h) (clauseAnchor c) c[k]) := by
  rw [edgeEntries_by_clauses,List.mem_flatMap]
  constructor
  · rintro ⟨⟨⟨h,c⟩,ci⟩,tagged,member⟩
    obtain ⟨⟨p,l⟩,lit,eq⟩ := List.mem_map.mp member
    have info := List.mem_zipIdx tagged
    have hc : (h,c)∈clauseEntries 1 f.clauses := by
      have bound : ci<(clauseEntries 1 f.clauses).length := by simpa using info.2.1
      have atIndex : (h,c)=(clauseEntries 1 f.clauses)[ci] := by simpa using info.2.2
      rw [atIndex]; exact List.getElem_mem _
    obtain ⟨k,hk,rfl,rfl⟩ := (literalEntries_mem_iff (h+1) c p l).mp lit
    refine ⟨h,c,hc,k,hk,?_⟩
    rw [clause_tag_rank f (h,c) ci tagged]
    exact eq.symm
  · rintro ⟨h,c,hc,k,hk,rfl⟩
    refine ⟨((h,c),Count.count clauseMarkExpr (FieldSavitch.suffix f) h),clause_tagged_member f h c hc,?_⟩
    apply List.mem_map.mpr
    exact ⟨(h+1+4*k,c[k]),(literalEntries_mem_iff (h+1) c _ _).mpr ⟨k,hk,rfl,rfl⟩,rfl⟩

end LeanTrominoes.PeriodicCNF.IncidenceFields
