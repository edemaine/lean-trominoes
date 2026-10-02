/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DominoGeometry
import LeanTrominoes.PeriodicMatchingDoubling

/-! # Fundamental-domain coordinates for periodic polycube subsets -/
namespace LeanTrominoes.Domino
open PeriodicLatticeGraph
variable {V : Type*} {d r : Nat}

structure Chart (V : Type*) (d r : Nat) where
  origin : V → Cell d
  period : Lattice r →+ Cell d
  injective : Function.Injective (fun x : V × Lattice r => origin x.1+period x.2)

def Chart.realize (C : Chart V d r) (x : V × Lattice r) : Cell d := C.origin x.1+C.period x.2
def Chart.region (C : Chart V d r) : Set (Cell d) := Set.range C.realize

theorem Chart.realize_translate (C : Chart V d r) (x : V × Lattice r) (t : Lattice r) :
    C.realize (translate t x)=C.realize x+C.period t := by
  simp [Chart.realize,translate,map_add,add_assoc]

theorem Chart.region_add (C : Chart V d r) {x : Cell d} (hx : x∈C.region) (t : Lattice r) :
    x+C.period t∈C.region := by
  obtain ⟨u,rfl⟩ := hx
  exact ⟨translate t u,C.realize_translate u t⟩

noncomputable def Chart.equivalence (C : Chart V d r) : (V × Lattice r) ≃ C.region :=
  Equiv.ofBijective (fun x => ⟨C.realize x,⟨x,rfl⟩⟩)
    ⟨fun _ _ h => C.injective (congrArg Subtype.val h),fun x => by
      obtain ⟨u,hu⟩ := x.property
      exact ⟨u,Subtype.ext hu⟩⟩

@[simp] theorem Chart.equivalence_val (C : Chart V d r) (x : V × Lattice r) :
    (C.equivalence x).val=C.realize x := rfl

@[simp] theorem Chart.realize_equivalence_symm (C : Chart V d r) (x : C.region) :
    C.realize (C.equivalence.symm x)=x.val :=
  congrArg Subtype.val (C.equivalence.apply_symm_apply x)

structure GraphChart (V : Type*) (d r : Nat) extends Chart V d r where
  arcs : List (Arc V r)
  adjacent_iff : ∀ x y, UndirectedAdj arcs x y ↔ Adjacent (origin x.1+period x.2) (origin y.1+period y.2)

theorem GraphChart.tileable_iff (C : GraphChart V d r) :
    Tileable C.toChart.region ↔ PeriodicLatticeGraph.HasPerfectMatching C.arcs := by
  rw [tileable_iff_pairing]
  constructor
  · rintro ⟨p,supported⟩
    refine ⟨p.transport C.toChart.equivalence,?_⟩
    intro x
    apply (C.adjacent_iff x _).mpr
    change Adjacent (C.toChart.realize x)
      (C.toChart.realize (C.toChart.equivalence.symm (p.mate (C.toChart.equivalence x))))
    rw [Chart.realize_equivalence_symm]
    exact supported (C.toChart.equivalence x)
  · rintro ⟨p,supported⟩
    refine ⟨p.transport C.toChart.equivalence.symm,?_⟩
    intro x
    have support := (C.adjacent_iff _ _).mp (supported (C.toChart.equivalence.symm x))
    change Adjacent (C.toChart.realize (C.toChart.equivalence.symm x))
      (C.toChart.realize (p.mate (C.toChart.equivalence.symm x))) at support
    rw [Chart.realize_equivalence_symm] at support
    exact support

def translatedTile (t : Cell d) (tile : Finset (Cell d)) : Finset (Cell d) := tile.image (fun x => x+t)
def PeriodicTiles (period : Lattice r →+ Cell d) (tiles : Set (Finset (Cell d))) : Prop :=
  ∀ tile∈tiles, ∀ t, translatedTile (period t) tile∈tiles

def doubledPeriod (period : Lattice r →+ Cell d) : Lattice r →+ Cell d where
  toFun t := period (t+t)
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; abel

theorem GraphChart.doubled_tiling [DecidableEq V] [Fintype V] (C : GraphChart V d r)
    (tiled : Tileable C.toChart.region) :
    ∃ tiles, IsTiling C.toChart.region tiles ∧ PeriodicTiles (doubledPeriod C.period) tiles := by
  let coloring := fun x => color (C.toChart.realize x)
  have proper : ProperColoring C.arcs coloring := fun x y edge => adjacent_color ((C.adjacent_iff x y).mp edge)
  have periodic : TwiceInvariant coloring := by
    intro x t
    change color (C.toChart.realize (translate (t+t) x))=color (C.toChart.realize x)
    rw [Chart.realize_translate,map_add,color_double]
  obtain ⟨p,supported,invariant⟩ := doubled_perfect_matching C.arcs coloring proper periodic
    (C.tileable_iff.mp tiled)
  let q := p.transport C.toChart.equivalence.symm
  have qSupported : ∀ x, Adjacent x.val (q.mate x).val := by
    intro x
    have support := (C.adjacent_iff _ _).mp (supported (C.toChart.equivalence.symm x))
    change Adjacent (C.toChart.realize (C.toChart.equivalence.symm x))
      (C.toChart.realize (p.mate (C.toChart.equivalence.symm x))) at support
    rw [Chart.realize_equivalence_symm] at support
    exact support
  refine ⟨pairingTiles q,pairing_isTiling q qSupported,?_⟩
  rintro tile ⟨x,rfl⟩ t
  let u := C.toChart.equivalence.symm x
  let y := C.toChart.equivalence (translate (t+t) u)
  refine ⟨y,?_⟩
  have xValue : C.toChart.realize u=x.val := by
    simpa only [Chart.equivalence_val] using congrArg Subtype.val (C.toChart.equivalence.apply_symm_apply x)
  have yValue : y.val=x.val+C.period (t+t) := by
    change C.toChart.realize (translate (t+t) u)=_
    rw [Chart.realize_translate,xValue]
  have mateValue : (q.mate y).val=(q.mate x).val+C.period (t+t) := by
    change C.toChart.realize (p.mate (C.toChart.equivalence.symm y))=C.toChart.realize (p.mate u)+_
    change C.toChart.realize (p.mate (C.toChart.equivalence.symm (C.toChart.equivalence (translate (t+t) u))))=_
    rw [Equiv.symm_apply_apply,invariant,Chart.realize_translate]
  simp only [translatedTile,Finset.image_insert,Finset.image_singleton,yValue,mateValue,doubledPeriod,AddMonoidHom.coe_mk,ZeroHom.coe_mk]

end LeanTrominoes.Domino
