/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationCNFCoordinates
import LeanTrominoes.PeriodicExactOneCNF

/-! # Finite clauses for local normalized orientation rules -/
namespace LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
open PeriodicOrthogonalDrawing

def differentClauses (l r : Bool → PeriodicLiteral Variable) : List (PeriodicClause Variable) :=
  [[l true,r true],[l false,r false]]

def equalClauses (l r : Bool → PeriodicLiteral Variable) : List (PeriodicClause Variable) :=
  [[l false,r true],[l true,r false]]

def localClauses (d : Drawing) (location : Cell) (kind : OrthogonalCellType) :
    List (PeriodicClause Variable) :=
  let literal := read d location
  match kind with
  | .blank => []
  | .wire .horizontal _ => differentClauses (literal .west) (literal .east)
  | .wire .vertical _ => differentClauses (literal .north) (literal .south)
  | .bend .northeast _ => differentClauses (literal .north) (literal .east)
  | .bend .northwest _ => differentClauses (literal .north) (literal .west)
  | .bend .southeast _ => differentClauses (literal .south) (literal .east)
  | .bend .southwest _ => differentClauses (literal .south) (literal .west)
  | .monochromaticVertex _ => PeriodicExactOneCNF.clause
      [literal .west true,literal .north true,literal .east true]
  | .trichromaticVertex _ => equalClauses (literal .west) (literal .north) ++
      equalClauses (literal .north) (literal .east)

private theorem different_correct (d : Drawing) (a : Variable → Cell → Bool)
    (first second : Cell) (s t : Side) (translate : Cell) :
    (∀ clause ∈ differentClauses (read d first s) (read d second t), clause.Holds a translate) ↔
      orientation d a (lift d first translate) s ≠ orientation d a (lift d second translate) t := by
  simp only [differentClauses,List.forall_mem_cons]
  simp [PeriodicClause.Holds,read_holds]
  cases orientation d a (lift d first translate) s <;>
    cases orientation d a (lift d second translate) t <;> decide

private theorem equal_correct (d : Drawing) (a : Variable → Cell → Bool)
    (location : Cell) (s t : Side) (translate : Cell) :
    (∀ clause ∈ equalClauses (read d location s) (read d location t), clause.Holds a translate) ↔
      orientation d a (lift d location translate) s = orientation d a (lift d location translate) t := by
  simp only [equalClauses,List.forall_mem_cons]
  simp [PeriodicClause.Holds,read_holds]
  cases orientation d a (lift d location translate) s <;>
    cases orientation d a (lift d location translate) t <;> decide

theorem localClauses_correct (d : Drawing) (a : Variable → Cell → Bool)
    (location translate : Cell) (kind : OrthogonalCellType) :
    (∀ clause ∈ localClauses d location kind, clause.Holds a translate) ↔
      satisfiesOrientation kind (orientation d a (lift d location translate)) := by
  cases kind with
  | blank => simp [localClauses,satisfiesOrientation]
  | wire axis color =>
      cases axis <;> exact different_correct d a location location _ _ translate
  | bend bend color =>
      cases bend <;> exact different_correct d a location location _ _ translate
  | monochromaticVertex color =>
      rw [localClauses,PeriodicExactOneCNF.clause_correct]
      simp only [PeriodicOneInThree.ClauseHolds,PeriodicOneInThree.ExactlyOne,
        PeriodicOneInThree.clauseValues,List.map_cons,List.map_nil,satisfiesOrientation]
      have truth (s : Side) :
          (a (read d location s true).atom (Cell.add translate (read d location s true).offset) ==
            (read d location s true).value) =
            orientation d a (lift d location translate) s := by
        have h := read_holds d a location translate s true
        simp only [PeriodicLiteral.Holds] at h
        have value : (read d location s true).value = true := rfl
        rw [value] at h ⊢
        cases first : a (read d location s true).atom (Cell.add translate (read d location s true).offset) <;>
          cases second : orientation d a (lift d location translate) s <;> simp_all
      rw [truth,truth,truth]
  | trichromaticVertex order =>
      simp only [localClauses,List.forall_mem_append,equal_correct,satisfiesOrientation]

def neighborClauses (d : Drawing) (location : Cell) (side : Side) : List (PeriodicClause Variable) :=
  if ((d.getAt location).portColor side).isSome then
    differentClauses (read d location side) (read d (latticeNeighbor location side) side.opposite)
  else []

theorem neighborClauses_correct (d : Drawing) (a : Variable → Cell → Bool)
    (location translate : Cell) (side : Side) :
    (∀ clause ∈ neighborClauses d location side, clause.Holds a translate) ↔
      (((d.getAt (lift d location translate)).portColor side).isSome →
        orientation d a (lift d location translate) side =
          !(orientation d a (latticeNeighbor (lift d location translate) side) side.opposite)) := by
  rw [getAt_lift,neighbor_lift]
  by_cases exposed : ((d.getAt location).portColor side).isSome
  · simp only [neighborClauses,exposed,ite_true,different_correct,true_implies]
    cases orientation d a (lift d location translate) side <;>
      cases orientation d a (lift d (latticeNeighbor location side) translate) side.opposite <;> decide
  · simp [neighborClauses,exposed]

end LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
