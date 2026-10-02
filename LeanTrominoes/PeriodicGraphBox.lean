/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicLatticeGraph

/-! # Lattice boxes and a finite pool containing every crossing edge -/
namespace LeanTrominoes.PeriodicLatticeGraph
variable {V : Type*} [DecidableEq V] [Fintype V] {d : Nat}

abbrev BoxCoordinates (d k : Nat) := Fin d → Fin k

def boxPoint {k : Nat} (a : BoxCoordinates d k) : Lattice d := fun i => (a i).val

theorem boxPoint_injective (k : Nat) : Function.Injective (boxPoint (d := d) (k := k)) := by
  intro a b h
  funext i
  apply Fin.ext
  have := congrFun h i
  exact_mod_cast (show (a i).val = (b i).val from by simpa [boxPoint] using this)

def box (d k : Nat) : Finset (Lattice d) := (Finset.univ : Finset (BoxCoordinates d k)).image boxPoint

theorem mem_box {k : Nat} {z : Lattice d} :
    z ∈ box d k ↔ ∀ i, 0 ≤ z i ∧ z i < k := by
  constructor
  · intro h
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h
    intro i; change 0 ≤ ((a i).val : Int) ∧ ((a i).val : Int) < k
    exact ⟨Int.natCast_nonneg _,by exact_mod_cast (a i).isLt⟩
  · intro h
    let a : BoxCoordinates d k := fun i => ⟨(z i).toNat,by have := h i; omega⟩
    refine Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩
    funext i
    exact Int.toNat_of_nonneg (h i).1

theorem card_box (d k : Nat) : (box d k).card = k^d := by
  rw [box,Finset.card_image_of_injective _ (boxPoint_injective k)]
  simp

def vertexBox (k : Nat) : Finset (V × Lattice d) := Finset.univ ×ˢ box d k

theorem mem_vertexBox {k : Nat} {x : V × Lattice d} :
    x ∈ vertexBox k ↔ x.2 ∈ box d k := by simp [vertexBox]

def rootBox (v : V) (k : Nat) : Finset (V × Lattice d) := (box d k).image fun z => (v,z)

theorem card_rootBox (v : V) (k : Nat) : (rootBox (d := d) v k).card = k^d := by
  rw [rootBox,Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.snd h),card_box]

/-- Coordinate locality; this includes the paper's Manhattan locality. -/
def Local (arcs : List (Arc V d)) : Prop := ∀ e ∈ arcs, ∀ i, (e.offset i).natAbs ≤ 1

def Arc.reverse (e : Arc V d) : Arc V d := ⟨e.target,e.source,-e.offset⟩

def facePoint (k : Nat) (e : Arc V d) (i : Fin d)
    (a : {j : Fin d // j ≠ i} → Fin k) : Lattice d := fun j =>
  if h : j = i then (if 0 < e.offset i then (k : Int)-1 else 0) else (a ⟨j,h⟩).val

def faceEdges (k : Nat) (e : Arc V d) (i : Fin d) : Finset ((V × Lattice d) × (V × Lattice d)) :=
  Finset.univ.image fun a : {j : Fin d // j ≠ i} → Fin k =>
    ((e.source,facePoint k e i a),(e.target,facePoint k e i a+e.offset))

theorem card_faceEdges (k : Nat) (e : Arc V d) (i : Fin d) :
    (faceEdges k e i).card ≤ k^(d-1) := by
  have count : Fintype.card {j : Fin d // j ≠ i} = d-1 := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_subtype_eq]
  calc
    (faceEdges k e i).card ≤ Fintype.card ({j : Fin d // j ≠ i} → Fin k) :=
      Finset.card_image_le
    _ = k^(d-1) := by simp [count]

def boundaryPool (arcs : List (Arc V d)) (k : Nat) : Finset ((V × Lattice d) × (V × Lattice d)) :=
  arcs.toFinset.biUnion fun e =>
    Finset.univ.biUnion fun orientation : Bool =>
      Finset.univ.biUnion fun i : Fin d => faceEdges k (if orientation then e.reverse else e) i

theorem card_boundaryPool (arcs : List (Arc V d)) (k : Nat) :
    (boundaryPool arcs k).card ≤ 2*d*arcs.length*k^(d-1) := by
  have one (e : Arc V d) (orientation : Bool) :
      (Finset.univ.biUnion fun i : Fin d => faceEdges k (if orientation then e.reverse else e) i).card ≤
        d*k^(d-1) := by
    apply (Finset.card_biUnion_le).trans
    calc
      _ ≤ ∑ _i : Fin d, k^(d-1) := Finset.sum_le_sum fun i _ => card_faceEdges k _ i
      _ = d*k^(d-1) := by simp
  have two (e : Arc V d) :
      (Finset.univ.biUnion fun o : Bool =>
        Finset.univ.biUnion fun i : Fin d => faceEdges k (if o then e.reverse else e) i).card ≤
        2*(d*k^(d-1)) := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _o : Bool, d*k^(d-1) := Finset.sum_le_sum fun o _ => one e o
      _ = 2*(d*k^(d-1)) := by simp
  unfold boundaryPool
  calc
    _ ≤ ∑ e ∈ arcs.toFinset, 2*(d*k^(d-1)) :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => two e)
    _ = arcs.toFinset.card*(2*(d*k^(d-1))) := by simp
    _ ≤ arcs.length*(2*(d*k^(d-1))) := Nat.mul_le_mul_right _ (List.toFinset_card_le arcs)
    _ = _ := by ring

theorem adj_crossing_face (e : Arc V d) (locality : ∀ i, (e.offset i).natAbs ≤ 1)
    (k : Nat) (z : Lattice d) (inside : z ∈ box d k) (outside : z+e.offset ∉ box d k) :
    ∃ i, ((e.source,z),(e.target,z+e.offset)) ∈ faceEdges k e i := by
  classical
  have zin := mem_box.mp inside
  have out : ∃ i, ¬ (0 ≤ (z+e.offset) i ∧ (z+e.offset) i < k) := by
    simpa only [mem_box,not_forall] using outside
  obtain ⟨i,hi⟩ := out
  have coordinate : z i = if 0 < e.offset i then (k : Int)-1 else 0 := by
    have iz := zin i
    have bound := locality i
    change ¬ (0 ≤ z i+e.offset i ∧ z i+e.offset i < k) at hi
    split_ifs <;> omega
  let a : {j : Fin d // j ≠ i} → Fin k := fun j => ⟨(z j).toNat,by have := zin j; omega⟩
  have equal : facePoint k e i a = z := by
    funext j
    by_cases h : j = i
    · subst j; simp only [facePoint,dif_pos rfl]; exact coordinate.symm
    · simp only [facePoint,dif_neg h,a,Int.toNat_of_nonneg (zin j).1]
  refine ⟨i,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩⟩
  rw [equal]

theorem crossing_mem_boundaryPool (arcs : List (Arc V d)) (locality : Local arcs)
    (k : Nat) (u v : V × Lattice d) (inside : u ∈ vertexBox k) (outside : v ∉ vertexBox k)
    (edge : UndirectedAdj arcs u v) : (u,v) ∈ boundaryPool arcs k := by
  classical
  have zin := mem_vertexBox.mp inside
  have zout : v.2 ∉ box d k := by simpa only [mem_vertexBox] using outside
  rcases edge with ⟨e,he,hs,ht,hz⟩ | ⟨e,he,hs,ht,hz⟩
  · obtain ⟨i,hi⟩ := adj_crossing_face e (locality e he) k u.2 zin (by simpa only [← hz] using zout)
    apply Finset.mem_biUnion.mpr ⟨e,List.mem_toFinset.mpr he,?_⟩
    apply Finset.mem_biUnion.mpr ⟨false,Finset.mem_univ _,?_⟩
    apply Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩
    change (u,v) ∈ faceEdges k e i
    have equal : ((e.source,u.2),(e.target,u.2+e.offset)) = (u,v) :=
      Prod.ext (Prod.ext hs rfl) (Prod.ext ht hz.symm)
    exact equal ▸ hi
  · have reverse_z : v.2 = u.2+e.reverse.offset := by
      change v.2 = u.2+-e.offset
      rw [hz]; abel
    have reverse_local : ∀ i, (e.reverse.offset i).natAbs ≤ 1 := by
      intro i; simpa [Arc.reverse] using locality e he i
    obtain ⟨i,hi⟩ := adj_crossing_face e.reverse reverse_local k u.2 zin
      (by simpa only [← reverse_z] using zout)
    apply Finset.mem_biUnion.mpr ⟨e,List.mem_toFinset.mpr he,?_⟩
    apply Finset.mem_biUnion.mpr ⟨true,Finset.mem_univ _,?_⟩
    apply Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩
    change (u,v) ∈ faceEdges k e.reverse i
    have equal : ((e.reverse.source,u.2),(e.reverse.target,u.2+e.reverse.offset)) = (u,v) :=
      Prod.ext (Prod.ext ht rfl) (Prod.ext hs reverse_z.symm)
    exact equal ▸ hi

end LeanTrominoes.PeriodicLatticeGraph
