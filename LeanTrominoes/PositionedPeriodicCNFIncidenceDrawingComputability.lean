/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedPeriodicCNFComputability
import LeanTrominoes.PeriodicGridDrawingComputability
import LeanTrominoes.PeriodicCNFIncidenceGraphComputability

/-! # Primitive recursive assembly of incidence drawings -/
namespace LeanTrominoes.PositionedPeriodicCNF
variable {A V : Type} [Primcodable A] [Primcodable V] [DecidableEq V]

theorem incidenceDrawing_primrec
    (source : A → PositionedPeriodicCNF V) (hs : Primrec source)
    (placement : A → PeriodicVariablePlacement V)
    (hp : Primrec fun a => (placement a).period)
    (hv : Primrec fun i : A × V => (placement i.1).position i.2)
    (routes : A → IncidenceRoutes)
    (hr : Primrec fun i : (A × Nat) × Nat => routes i.1.1 i.1.2 i.2) :
    Primrec fun a => incidenceDrawing (source a) (placement a) (routes a) := by
  have atoms : Primrec fun a => (source a).erase.variableOccurrences.dedup :=
    PeriodicThreeSATThree.dedup_primrec.comp
      (PeriodicCNF.variableOccurrences_primrec.comp (erase_primrec.comp hs))
  have vars : Primrec fun a =>
      (source a).erase.variableOccurrences.dedup.map (placement a).position :=
    Primrec.list_map atoms hv.to₂
  have clauses := clauses_primrec.comp hs
  have clausePos : Primrec fun i : A × PositionedPeriodicClause V =>
      canonicalClausePosition (placement i.1) i.2 :=
    (canonicalClausePosition_primrec (fun a => (placement a).period) hp).of_eq fun _ => rfl
  have positions : Primrec fun a => incidenceVertexPositions (source a) (placement a) := by
    exact (Primrec.list_append.comp vars (Primrec.list_map clauses clausePos.to₂)).of_eq
      fun a => by simp only [incidenceVertexPositions,PeriodicCNF.incidenceVariableVertices,
        List.map_map]; rfl
  have row : Primrec fun i : A × (PositionedPeriodicClause V × Nat) =>
      i.2.1.literals.zipIdx.map (fun l => routes i.1 i.2.2 l.2) := by
    apply Primrec.list_map (PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp (Primrec.fst.comp Primrec.snd)))
    exact (hr.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd))).to₂
  have edges : Primrec fun a => incidenceEdgeRoutes (source a) (routes a) :=
    Primrec.list_flatMap (PeriodicThreeSATThree.zipIdx_primrec.comp clauses) row.to₂
  exact (PeriodicGridDrawing.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.nat_sub.comp hp (Primrec.const 1)) (Primrec.pair positions edges))).of_eq fun _ => rfl

end LeanTrominoes.PositionedPeriodicCNF
