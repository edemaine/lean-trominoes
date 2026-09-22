/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedIncidenceRows
import LeanTrominoes.UnaryColumnSerialization

/-! # Clause headers aligned with their first literal occurrence -/
namespace LeanTrominoes.PositionedIncidenceRows
open UnaryFieldEncoderMachine

def headerBlocks (arity : Nat) : List (List Symbol) :=
  (List.range arity).map (fun i => if i = 0 then unaryField arity else [])

def header {V : Type*} (row : Row V) : List Symbol :=
  if row.2.2 = 0 then unaryField row.1.1.literals.length else []

private theorem map_indices {A B : Type*} (values : List A) (f : Nat → B) :
    values.zipIdx.map (fun p => f p.2) = (List.range values.length).map f := by
  simpa only [List.map_map, Function.comp_def, List.range'_eq_map_range, Nat.zero_add,
    List.map_id_fun] using congrArg (List.map f) (List.zipIdx_map_snd 0 values)

theorem headers_eq_lengths {V : Type*} (source : PositionedPeriodicCNF V) :
    (rows source).map header = (source.erase.clauses.map List.length).flatMap headerBlocks := by
  simp only [rows, List.map_flatMap, List.map_map, Function.comp_def, header]
  have inner (c : PositionedPeriodicClause V) :
      c.literals.zipIdx.map (fun l => if l.2 = 0 then unaryField c.literals.length else []) =
      headerBlocks c.literals.length :=
    map_indices c.literals (fun i => if i = 0 then unaryField c.literals.length else [])
  simp_rw [inner]
  have dropped := congrArg (fun cs : List (PositionedPeriodicClause V) =>
    cs.flatMap (fun c => headerBlocks c.literals.length)) (List.zipIdx_map_fst 0 source.clauses)
  simpa only [List.flatMap_map, PositionedPeriodicCNF.erase, List.map_map, Function.comp_def] using dropped

end LeanTrominoes.PositionedIncidenceRows
