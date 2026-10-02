/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDominoNeighbors

/-! # Corollary 5.14: periodic domino completion with doubled periods -/
namespace LeanTrominoes.Domino
open PeriodicLatticeGraph
variable {V : Type*} {d r : Nat}

def Occupied (tiles : Set (Finset (Cell d))) (x : Cell d) : Prop := ∃ tile∈tiles, x∈tile
def Completable (region : Set (Cell d)) (prefill : Set (Finset (Cell d))) : Prop :=
  ∃ tiles, IsTiling region tiles ∧ prefill⊆tiles

theorem occupied_add_iff (period : Lattice r →+ Cell d) (tiles : Set (Finset (Cell d)))
    (periodic : PeriodicTiles period tiles) (x : Cell d) (t : Lattice r) :
    Occupied tiles (x+period t) ↔ Occupied tiles x := by
  constructor
  · rintro ⟨tile,ht,hx⟩
    refine ⟨translatedTile (period (-t)) tile,periodic tile ht (-t),?_⟩
    apply Finset.mem_image.mpr
    exact ⟨x+period t,hx,by simp⟩
  · rintro ⟨tile,ht,hx⟩
    exact ⟨translatedTile (period t) tile,periodic tile ht t,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩

abbrev FreeVertices (C : Chart V d r) (prefill : Set (Finset (Cell d))) :=
  {v : V // ¬ Occupied prefill (C.origin v)}

def Chart.freeChart (C : Chart V d r) (prefill : Set (Finset (Cell d))) : Chart (FreeVertices C prefill) d r where
  origin v := C.origin v.val
  period := C.period
  injective := by
    intro x y equal
    have same : (x.1.val,x.2)=(y.1.val,y.2) := C.injective (by exact equal)
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst same)
    · exact congrArg (fun z : V × Lattice r => z.2) same

theorem Chart.freeChart_region (C : Chart V d r) (prefill : Set (Finset (Cell d)))
    (periodic : PeriodicTiles C.period prefill) (x : Cell d) :
    x∈(C.freeChart prefill).region ↔ x∈C.region ∧ ¬ Occupied prefill x := by
  constructor
  · rintro ⟨⟨v,z⟩,rfl⟩
    refine ⟨⟨(v.val,z),rfl⟩,?_⟩
    exact fun h => v.property ((occupied_add_iff C.period prefill periodic (C.origin v.val) z).mp h)
  · rintro ⟨⟨⟨v,z⟩,rfl⟩,free⟩
    have freeOrigin : ¬Occupied prefill (C.origin v) := fun h =>
      free ((occupied_add_iff C.period prefill periodic (C.origin v) z).mpr h)
    exact ⟨(⟨v,freeOrigin⟩,z),rfl⟩

theorem IsTiling.same_tile {region : Set (Cell d)} {tiles : Set (Finset (Cell d))}
    (tiling : IsTiling region tiles) {a b : Finset (Cell d)} (ha : a∈tiles) (hb : b∈tiles)
    {x : Cell d} (xa : x∈a) (xb : x∈b) : a=b := by
  obtain ⟨tile,_,unique⟩ := tiling.covers x ((tiling.inside a ha).2 x xa)
  exact (unique a ⟨ha,xa⟩).trans (unique b ⟨hb,xb⟩).symm

theorem Chart.freeChart_tileable (C : Chart V d r) (prefill : Set (Finset (Cell d)))
    (periodic : PeriodicTiles C.period prefill) (completion : Completable C.region prefill) :
    Tileable (C.freeChart prefill).region := by
  obtain ⟨tiles,tiling,extension⟩ := completion
  refine ⟨{tile | tile∈tiles ∧ tile∉prefill},?_,?_⟩
  · intro tile ht
    refine ⟨(tiling.inside tile ht.1).1,?_⟩
    intro x hx
    apply (C.freeChart_region prefill periodic x).mpr
    refine ⟨(tiling.inside tile ht.1).2 x hx,?_⟩
    rintro ⟨other,ho,hxo⟩
    exact ht.2 ((tiling.same_tile ht.1 (extension ho) hx hxo) ▸ ho)
  · intro x hx
    obtain ⟨inside,free⟩ := (C.freeChart_region prefill periodic x).mp hx
    obtain ⟨tile,ht,unique⟩ := tiling.covers x inside
    refine ⟨tile,⟨⟨ht.1,fun h => free ⟨tile,h,ht.2⟩⟩,ht.2⟩,?_⟩
    intro other ho
    exact unique other ⟨ho.1.1,ho.2⟩

/-- The prefill remains fixed, and only the free cells are retiled. -/
theorem Chart.doubled_completion [DecidableEq V] [Fintype V] (C : Chart V d r)
    (prefill : Set (Finset (Cell d))) (periodic : PeriodicTiles C.period prefill)
    (completion : Completable C.region prefill) :
    ∃ tiles, IsTiling C.region tiles ∧ prefill⊆tiles ∧ PeriodicTiles (doubledPeriod C.period) tiles := by
  classical
  obtain ⟨original,originalTiling,extension⟩ := completion
  obtain ⟨rest,restTiling,restPeriodic⟩ := (C.freeChart prefill).doubled_tiling
    (C.freeChart_tileable prefill periodic ⟨original,originalTiling,extension⟩)
  refine ⟨prefill∪rest,?_,Set.subset_union_left,?_⟩
  · constructor
    · intro tile ht
      rcases ht with hp | hr
      · exact originalTiling.inside tile (extension hp)
      · refine ⟨(restTiling.inside tile hr).1,?_⟩
        intro x hx
        exact ((C.freeChart_region prefill periodic x).mp ((restTiling.inside tile hr).2 x hx)).1
    · intro x hx
      by_cases occupied : Occupied prefill x
      · obtain ⟨tile,ht,hxt⟩ := occupied
        refine ⟨tile,⟨Or.inl ht,hxt⟩,?_⟩
        intro other ho
        rcases ho.1 with hp | hr
        · exact originalTiling.same_tile (extension hp) (extension ht) ho.2 hxt
        · have free := ((C.freeChart_region prefill periodic x).mp ((restTiling.inside other hr).2 x ho.2)).2
          exact (free ⟨tile,ht,hxt⟩).elim
      · have freeRegion := (C.freeChart_region prefill periodic x).mpr ⟨hx,occupied⟩
        obtain ⟨tile,ht,unique⟩ := restTiling.covers x freeRegion
        refine ⟨tile,⟨Or.inr ht.1,ht.2⟩,?_⟩
        intro other ho
        rcases ho.1 with hp | hr
        · exact (occupied ⟨other,hp,ho.2⟩).elim
        · exact unique other ⟨hr,ho.2⟩
  · intro tile ht t
    rcases ht with hp | hr
    · exact Or.inl (periodic tile hp (t+t))
    · exact Or.inr (restPeriodic tile hr t)

end LeanTrominoes.Domino
