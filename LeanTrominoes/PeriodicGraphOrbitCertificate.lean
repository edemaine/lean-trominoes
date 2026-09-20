/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGraphDrawingCertificate
import LeanTrominoes.PositionedPeriodicCNFIncidenceDrawingComputability

/-! # Finite compatibility checks independent of vertex representatives

Representatives may lie outside the fundamental square. Their residues must
be pairwise distinct, so the infinite periodic vertex placement is injective.
-/
namespace LeanTrominoes.PeriodicGridDrawing.OrbitCertificate
open Computability

def residue (period : Nat) (p : Cell) : Cell := (p.1 % period,p.2 % period)

theorem residue_eq_iff (period : Nat) (p q : Cell) :
    residue period p = residue period q ↔ ∃ t, p = Cell.add (Cell.scale period t) q := by
  constructor
  · intro h
    refine ⟨(p.1/period-q.1/period,p.2/period-q.2/period),?_⟩
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    have px := Int.mul_ediv_add_emod p.1 period
    have py := Int.mul_ediv_add_emod p.2 period
    have qx := Int.mul_ediv_add_emod q.1 period
    have qy := Int.mul_ediv_add_emod q.2 period
    apply Prod.ext <;> simp only [Cell.add,Cell.scale]
    · change p.1 % period = q.1 % period at hx
      nlinarith
    · change p.2 % period = q.2 % period at hy
      nlinarith
  · rintro ⟨t,rfl⟩
    simp [residue,Cell.add,Cell.scale,Int.add_emod]

theorem residue_primrec : Primrec₂ residue := by
  have coordinate : Primrec₂ fun n : Nat => fun x : Int => x % (n : Int) := by
    have h := int_subtract_primrec.comp₂ Primrec₂.right
      (int_multiply_primrec.comp₂ (int_ofNat_primrec.comp₂ Primrec₂.left)
        (int_edivNat_primrec.comp₂ Primrec₂.right Primrec₂.left))
    exact h.of_eq fun n x => by
      change x - (n : Int) * (x / (n : Int)) = x % (n : Int)
      have identity := Int.mul_ediv_add_emod x (n : Int)
      nlinarith
  exact Primrec₂.pair.comp₂
    (coordinate.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
    (coordinate.comp₂ Primrec₂.left (Primrec.snd.comp₂ Primrec₂.right))

variable {V : Type} [DecidableEq V]
def Compatible (g : PeriodicGraph V) (d : PeriodicGridDrawing) : Prop :=
  d.vertexPositions.length = g.vertices.length ∧
  d.edgeRoutes.length = g.edges.length ∧
  (d.vertexPositions.map (residue d.gridSize)).Nodup ∧ d.RoutesMatch g

theorem compatible_primrec [Primcodable V] : PrimrecRel (Compatible (V := V)) := by
  have residues : Primrec fun i : PeriodicGraph V × PeriodicGridDrawing =>
      i.2.vertexPositions.map (residue i.2.gridSize) :=
    Primrec.list_map (vertexPositions_primrec.comp Primrec.snd)
      (residue_primrec.comp (gridSize_primrec.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
  have nodup := (Primrec.eq.comp (PeriodicThreeSATThree.dedup_primrec.comp residues) residues).of_eq
    (fun _ => List.dedup_eq_self)
  exact (Primrec.eq.comp (Primrec.list_length.comp (vertexPositions_primrec.comp Primrec.snd))
    (Primrec.list_length.comp (PeriodicGraph.vertices_primrec.comp Primrec.fst))).and
    ((Primrec.eq.comp (Primrec.list_length.comp (edgeRoutes_primrec.comp Primrec.snd))
      (Primrec.list_length.comp (PeriodicGraph.edges_primrec.comp Primrec.fst))).and
    (nodup.and (FiniteCertificate.routesMatch_primrec.comp Primrec.fst Primrec.snd)))

/-- Distinct entries cannot coincide under any periodic translation. -/
theorem vertex_orbits_injective {g : PeriodicGraph V} {d : PeriodicGridDrawing}
    (h : Compatible g d) (i j : Fin d.vertexPositions.length) (t : Cell)
    (eq : d.vertexPositions[i] = Cell.add (d.periodTranslation t) d.vertexPositions[j]) : i = j := by
  have same := (residue_eq_iff d.gridSize _ _).2 ⟨t,eq⟩
  have inj := List.nodup_iff_injective_getElem.mp h.2.2.1
  have result := @inj ⟨i.val,by simpa using i.isLt⟩ ⟨j.val,by simpa using j.isLt⟩
  apply Fin.ext
  exact congrArg (fun k : Fin (d.vertexPositions.map (residue d.gridSize)).length => k.val)
    (result (by simpa using same))

end LeanTrominoes.PeriodicGridDrawing.OrbitCertificate
