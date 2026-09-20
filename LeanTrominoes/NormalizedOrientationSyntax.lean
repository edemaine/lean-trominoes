/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetReductionComputability
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificateComputability

/-! # Effective validity checks for normalized periodic orientation drawings -/
namespace LeanTrominoes.Gadget.NormalizedOrientation
open PeriodicOrthogonalDrawing
set_option maxHeartbeats 1000000

abbrev Drawing := PeriodicOrthogonalDrawing

def sides : List Side := [.north,.east,.south,.west]

theorem mem_sides (s : Side) : s ∈ sides := by cases s <;> simp [sides]

def nextX (d : Drawing) (x : Nat) (s : Side) : Nat :=
  if s = .east then (x+1) % d.horizontalPeriod
  else if s = .west then (d.horizontalPeriod - 1 % d.horizontalPeriod + x) % d.horizontalPeriod else x

def nextY (d : Drawing) (y : Nat) (s : Side) : Nat :=
  if s = .south then (y+1) % d.verticalPeriod
  else if s = .north then (d.verticalPeriod - 1 % d.verticalPeriod + y) % d.verticalPeriod else y

theorem next_eq (d : Drawing) (p : d.Position) (s : Side) :
    (nextX d p.1.val s, nextY d p.2.val s) =
      ((d.neighbor p s).1.val, (d.neighbor p s).2.val) := by
  cases s <;> simp [nextX, nextY, neighbor, Fin.add_def, Fin.sub_def,
    horizontalPeriod, verticalPeriod]

def Checks (d : Drawing) : Prop :=
  d.cellTypes.length = d.horizontalPeriod * d.verticalPeriod ∧
  ∀ x ∈ List.range d.horizontalPeriod, ∀ y ∈ List.range d.verticalPeriod, ∀ s ∈ sides,
    (d.indexedCellType x y).portColor s =
      (d.indexedCellType (nextX d x s) (nextY d y s)).portColor s.opposite ∧
    ((d.indexedCellType x y).isVertex = true →
      (d.indexedCellType (nextX d x s) (nextY d y s)).isVertex = false)

theorem checks_iff (d : Drawing) : Checks d ↔ d.IsWellFormed ∧ d.VerticesSeparated := by
  have eq (p : d.Position) (s : Side) :
      d.indexedCellType (nextX d p.1.val s) (nextY d p.2.val s) = d.get (d.neighbor p s) := by
    have h := next_eq d p s
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp only at hx hy
    rw [hx,hy]
    rfl
  have here (p : d.Position) : d.indexedCellType p.1.val p.2.val = d.get p := rfl
  constructor
  · rintro ⟨len, all⟩
    refine ⟨⟨len, ?_⟩, ?_⟩
    · intro p s
      have h := (all p.1.val (List.mem_range.mpr p.1.isLt)
        p.2.val (List.mem_range.mpr p.2.isLt) s (mem_sides s)).1
      simpa only [eq, here] using h
    · intro p s
      have h := (all p.1.val (List.mem_range.mpr p.1.isLt)
        p.2.val (List.mem_range.mpr p.2.isLt) s (mem_sides s)).2
      simpa only [eq, here] using h
  · rintro ⟨⟨len, ports⟩, separated⟩
    refine ⟨len, ?_⟩
    intro x hx y hy s _
    let p : d.Position := (⟨x,List.mem_range.mp hx⟩,⟨y,List.mem_range.mp hy⟩)
    change (d.get p).portColor s = _ ∧ ((d.get p).isVertex = true → _)
    have he := eq p s
    dsimp only [p] at he
    rw [he]
    exact ⟨ports p s, separated p s⟩

noncomputable local instance : Primcodable Side :=
  Primcodable.ofEquiv (Fin (Fintype.card Side)) (Fintype.equivFin Side)

private theorem next_primrec (period : Drawing → Nat) (hp : Primrec period)
    (forward backward : Side) :
    Primrec fun p : Drawing × Nat × Side =>
      if p.2.2 = forward then (p.2.1+1) % period p.1
      else if p.2.2 = backward then
        (period p.1 - 1 % period p.1 + p.2.1) % period p.1 else p.2.1 := by
  let n : Primrec (fun p : Drawing × Nat × Side => period p.1) := hp.comp Primrec.fst
  let x : Primrec (fun p : Drawing × Nat × Side => p.2.1) := Primrec.fst.comp Primrec.snd
  let side : Primrec (fun p : Drawing × Nat × Side => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp side (Primrec.const forward))
    (Primrec.nat_mod.comp (Primrec.nat_add.comp x (Primrec.const 1)) n)
    (Primrec.ite (Primrec.eq.comp side (Primrec.const backward))
      (Primrec.nat_mod.comp (Primrec.nat_add.comp
        (Primrec.nat_sub.comp n (Primrec.nat_mod.comp (Primrec.const 1) n)) x) n) x)

theorem checks_primrec : PrimrecPred Checks := by
  have nx : Primrec fun p : Drawing × Nat × Side => nextX p.1 p.2.1 p.2.2 :=
    next_primrec horizontalPeriod periodicOrthogonalDrawing_horizontalPeriod_primrec .east .west
  have ny : Primrec fun p : Drawing × Nat × Side => nextY p.1 p.2.1 p.2.2 :=
    next_primrec verticalPeriod periodicOrthogonalDrawing_verticalPeriod_primrec .south .north
  let d : Primrec (fun p : ((Drawing × Nat) × Nat) × Side => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let x : Primrec (fun p : ((Drawing × Nat) × Nat) × Side => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let y : Primrec (fun p : ((Drawing × Nat) × Nat) × Side => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  let here := indexedCellType_primrec.comp (Primrec.pair d (Primrec.pair x y))
  let there := indexedCellType_primrec.comp (Primrec.pair d (Primrec.pair
    (nx.comp (Primrec.pair d (Primrec.pair x Primrec.snd)))
    (ny.comp (Primrec.pair d (Primrec.pair y Primrec.snd)))))
  have ports : Primrec₂ OrthogonalCellType.portColor := Primrec.dom_finite _
  have vertex : Primrec OrthogonalCellType.isVertex := Primrec.dom_finite _
  have opposite : Primrec Side.opposite := Primrec.dom_finite _
  have row : PrimrecPred fun p : ((Drawing × Nat) × Nat) × Side =>
      (p.1.1.1.indexedCellType p.1.1.2 p.1.2).portColor p.2 =
        (p.1.1.1.indexedCellType (nextX p.1.1.1 p.1.1.2 p.2)
          (nextY p.1.1.1 p.1.2 p.2)).portColor p.2.opposite ∧
      ((p.1.1.1.indexedCellType p.1.1.2 p.1.2).isVertex = true →
        (p.1.1.1.indexedCellType (nextX p.1.1.1 p.1.1.2 p.2)
          (nextY p.1.1.1 p.1.2 p.2)).isVertex = false) := by
    apply ((Primrec.eq.comp (ports.comp here Primrec.snd)
      (ports.comp there (opposite.comp Primrec.snd))).and
      ((Primrec.eq.comp (vertex.comp here) (Primrec.const true)).not.or
        (Primrec.eq.comp (vertex.comp there) (Primrec.const false)))).of_eq
    intro p
    exact and_congr_right fun _ => imp_iff_not_or.symm
  have hs := primrecPred_forall_mem (Primrec.const sides) row.primrecRel
  have hy := primrecPred_forall_mem
    (Primrec.list_range.comp (periodicOrthogonalDrawing_verticalPeriod_primrec.comp Primrec.fst))
    hs.primrecRel
  have hx := primrecPred_forall_mem
    (Primrec.list_range.comp periodicOrthogonalDrawing_horizontalPeriod_primrec) hy.primrecRel
  exact (Primrec.eq.comp
    (Primrec.list_length.comp periodicOrthogonalDrawing_cellTypes_primrec)
    (Primrec.nat_mul.comp periodicOrthogonalDrawing_horizontalPeriod_primrec
      periodicOrthogonalDrawing_verticalPeriod_primrec)).and hx

end LeanTrominoes.Gadget.NormalizedOrientation
