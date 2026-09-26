/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTemplateFirstBroadcast
import LeanTrominoes.PositionedIncidenceRows
import LeanTrominoes.UnaryColumnCompiler

/-! # Broadcasting a clause's first incidence value across its literals -/
noncomputable section
namespace LeanTrominoes.PositionedIncidenceRows
open Turing UnaryColumn

def clauseValueRows {Variable : Type} (source : PositionedPeriodicCNF Variable) (value : Row Variable → Nat) :
    List (List Nat) := source.clauses.zipIdx.map (fun clause =>
      clause.1.literals.zipIdx.map (fun literal => value (clause, literal)))

def firstValue {Variable : Type} (value : Row Variable → Nat) (row : Row Variable) : Nat :=
  (row.1.1.literals.zipIdx.map (fun literal => value (row.1, literal))).headD 0

theorem clauseValueRows_flatten {Variable : Type} (source : PositionedPeriodicCNF Variable) (value : Row Variable → Nat) :
    (clauseValueRows source value).flatten = (rows source).map value := by
  simp only [clauseValueRows, ← List.flatMap_def, rows, List.map_flatMap, List.map_map, Function.comp_def]

theorem clauseValueRows_lengths {Variable : Type} (source : PositionedPeriodicCNF Variable) (value : Row Variable → Nat) :
    (clauseValueRows source value).map List.length = source.erase.clauses.map List.length := by
  simp only [clauseValueRows, List.map_map, List.length_map, List.length_zipIdx,
    PositionedPeriodicCNF.erase, Function.comp_def]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (fun c : PositionedPeriodicClause Variable => c.literals.length)) (List.zipIdx_map_fst 0 source.clauses)

theorem clauseValueRows_broadcast {Variable : Type} (source : PositionedPeriodicCNF Variable) (value : Row Variable → Nat) :
    (clauseValueRows source value).flatMap (fun block => List.replicate block.length (block.headD 0)) =
      (rows source).map (firstValue value) := by
  simp only [clauseValueRows, List.flatMap_map, List.length_map, List.length_zipIdx,
    rows, List.map_flatMap, List.map_map, Function.comp_def, firstValue, List.map_const']

theorem firstValue_cons {Variable : Type} (value : Row Variable → Nat) (row : Row Variable)
    (literal : PeriodicLiteral Variable) (rest : List (PeriodicLiteral Variable))
    (eq : row.1.1.literals = literal :: rest) : firstValue value row = value (row.1, (literal, 0)) := by
  simp only [firstValue, eq, List.zipIdx_cons, List.map_cons, List.headD_cons]

def firstColumnCompiler {Symbol Variable Profile : Type} [Fintype Symbol] [Inhabited Symbol]
    [Fintype Profile] [Inhabited Profile]
    (source : List Symbol → PositionedPeriodicCNF Variable) (profiles : List Symbol → List Profile)
    (size : Profile → Nat)
    (aligned : ∀ s, (source s).erase.clauses.map List.length = (profiles s).map size)
    (profileCompiler : TM2ComputableInPolyTime id id profiles)
    (value : List Symbol → Row Variable → Nat)
    (valueCompiler : Compiler (fun s => rows (source s)) value) :
    Compiler (fun s => rows (source s)) (fun s => firstValue (value s)) := by
  let physical := FiniteTemplateFirstBroadcast.of_lengths id size profiles
    (fun s => clauseValueRows (source s) (value s))
    (fun s => (clauseValueRows_lengths _ _).trans (aligned s)) profileCompiler
    (TM2ComputableInPolyTime.of_eq valueCompiler (fun s => (clauseValueRows_flatten _ _).symm))
  exact TM2ComputableInPolyTime.of_eq physical (fun s => clauseValueRows_broadcast _ _)

end LeanTrominoes.PositionedIncidenceRows
end
