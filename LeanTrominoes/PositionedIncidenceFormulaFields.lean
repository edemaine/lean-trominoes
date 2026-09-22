/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedIncidenceRows
import LeanTrominoes.PeriodicCNFFlatEncoding
import LeanTrominoes.PeriodicCNFInjectiveRenaming

/-! # Native formula fields assembled in geometric incidence order -/
namespace LeanTrominoes.PositionedIncidenceRows
open PeriodicCNFFlatEncoding

def namedLiteral {V : Type*} (name : V → Nat) (row : Row V) : PeriodicLiteral Nat :=
  (row.2.1.anchorNormalize (PeriodicCNF.clauseAnchor row.1.1.literals)).rename name

def rowFields {V : Type*} (name : V → Nat) (row : Row V) : List Nat :=
  (if row.2.2 = 0 then [row.1.1.literals.length] else []) ++ literalFields (namedLiteral name row)

theorem map_literals {V O : Type*} (source : PositionedPeriodicCNF V) (f : PeriodicLiteral V → O) :
    (rows source).map (fun row => f row.2.1) = source.erase.clauses.flatMap (fun c => c.map f) := by
  simp only [rows, List.map_flatMap, List.map_map, Function.comp_def]
  have each (c : PositionedPeriodicClause V) : c.literals.zipIdx.map (fun l => f l.1) = c.literals.map f := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map f) (List.zipIdx_map_fst 0 c.literals)
  simp_rw [each]
  have dropped := congrArg (fun cs : List (PositionedPeriodicClause V) => cs.flatMap (fun c => c.literals.map f))
    (List.zipIdx_map_fst 0 source.clauses)
  simpa only [List.flatMap_map, PositionedPeriodicCNF.erase] using dropped

private theorem frame_clause {A : Type*} (values : List A) (nonempty : values ≠ []) (f : A → List Nat) :
    values.zipIdx.flatMap (fun p => (if p.2 = 0 then [values.length] else []) ++ f p.1) =
      values.length :: values.flatMap f := by
  cases values with
  | nil => contradiction
  | cons first rest =>
    have tail : (rest.zipIdx 1).flatMap
        (fun p => (if p.2 = 0 then [(first :: rest).length] else []) ++ f p.1) = rest.flatMap f := by
      calc
        _ = (rest.zipIdx 1).flatMap (fun p => f p.1) := by
          apply List.flatMap_congr
          intro p hp
          have index : p.2 ∈ List.range' 1 rest.length := by
            rw [← List.zipIdx_map_snd 1 rest]
            exact List.mem_map.mpr ⟨p, hp, rfl⟩
          obtain ⟨i, _, indexEq⟩ := List.mem_range'.mp index
          have ne : p.2 ≠ 0 := by omega
          simp only [ne, if_false, List.nil_append]
        _ = rest.flatMap f := by rw [← List.flatMap_map, List.zipIdx_map_fst]
    simpa only [List.zipIdx_cons, List.flatMap_cons, Nat.zero_add,
      ↓reduceIte, List.singleton_append, List.cons_append, List.nil_append] using congrArg (fun xs => (first :: rest).length :: (f first ++ xs)) tail

/-- With no empty clauses, each clause header belongs to its first occurrence.
Renaming and anchor normalization preserve exactly this serialized order. -/
theorem formulaFields_eq {V : Type*} (source : PositionedPeriodicCNF V) (name : V → Nat)
    (nonempty : ∀ c ∈ source.clauses, c.literals ≠ []) :
    formulaFields (source.erase.anchorNormalize.rename name) =
      source.clauses.length :: (rows source).flatMap (rowFields name) := by
  have clauseEq (c : PositionedPeriodicClause V) (hc : c ∈ source.clauses) :
      c.literals.zipIdx.flatMap (fun l => rowFields name ((c, 0), l)) =
        clauseFields (PeriodicCNF.renameClause name c.literals.anchorNormalize) := by
    rw [show clauseFields (PeriodicCNF.renameClause name c.literals.anchorNormalize) =
      c.literals.length :: c.literals.flatMap (fun l => literalFields
        ((l.anchorNormalize (PeriodicCNF.clauseAnchor c.literals)).rename name)) by
          simp [clauseFields, PeriodicCNF.renameClause, PeriodicClause.anchorNormalize,
            List.flatMap_map, List.map_map]]
    simpa only [rowFields, namedLiteral] using frame_clause c.literals (nonempty c hc)
      (fun l => literalFields ((l.anchorNormalize (PeriodicCNF.clauseAnchor c.literals)).rename name))
  have body : (rows source).flatMap (rowFields name) =
      source.clauses.flatMap (fun c => clauseFields (PeriodicCNF.renameClause name c.literals.anchorNormalize)) := by
    unfold rows
    rw [List.flatMap_assoc]
    have unindex := congrArg (fun cs : List (PositionedPeriodicClause V) =>
      cs.flatMap (fun c => clauseFields (PeriodicCNF.renameClause name c.literals.anchorNormalize)))
      (List.zipIdx_map_fst 0 source.clauses)
    rw [List.flatMap_map] at unindex
    rw [← unindex]
    apply List.flatMap_congr
    intro c hc
    rw [List.flatMap_map]
    exact clauseEq c.1 (List.fst_mem_of_mem_zipIdx hc)
  rw [body]
  simp [formulaFields, PeriodicCNF.rename, PeriodicCNF.anchorNormalize,
    PositionedPeriodicCNF.erase, List.flatMap_map, List.map_map]

end LeanTrominoes.PositionedIncidenceRows
