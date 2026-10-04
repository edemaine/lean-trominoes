/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteIBrickPrefill
import LeanTrominoes.FiniteIBrickNetworkExtraction
import LeanTrominoes.FiniteBrickNeighborhood
import LeanTrominoes.GadgetAssembly

/-! # A fixed finite neighborhood suffices to read a brick's Boolean network -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
open IBricks
set_option maxHeartbeats 2000000

theorem regionAt_bounds (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry∈layout (palette location)) {c : Cell}
    (member : c∈regionAt location entry) :
    (origin location).1≤c.1 ∧ c.1<(origin location).1+36 ∧
      (origin location).2≤c.2 ∧ c.2≤(origin location).2+162 := by
  change c∈entry.1.pattern.region.image (Cell.add (Cell.add (origin location) entry.2)) at member
  rw [← group_at_region palette location he] at member
  obtain ⟨m,owned,micro⟩ := Finset.mem_biUnion.mp member
  obtain ⟨localCell,localMember,rfl⟩ := Finset.mem_image.mp owned
  have bounds := local_groups_inside (palette location) entry he localMember
  simp only [brickMicroCells,Finset.mem_product,Finset.mem_Ico] at bounds
  rw [mem_microRegion] at micro
  dsimp [Cell.add,brickMicroOrigin,origin] at micro ⊢
  unfold MemberAt at micro
  omega

theorem portal_brick_bounds (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry∈layout (palette location)) {p : Cell}
    (hp : p∈entry.1.portCells) (right : Bool) :
    let c := portalCell (Cell.add (atomMicroOffset location entry) p) right
    (origin location).1≤c.1 ∧ c.1<(origin location).1+36 ∧
      (origin location).2≤c.2 ∧ c.2≤(origin location).2+162 := by
  have bounds := brick_port_window (palette location) entry he p hp
  simp only [Finset.mem_product,Finset.mem_Ico] at bounds
  cases right <;> dsimp [portalCell,atomMicroOffset,brickMicroOrigin,origin,Cell.add] at bounds ⊢ <;> omega

private theorem nearNeighbor {center other : Cell} (near : BrickNear 3 center other)
    {delta : Cell} (member : delta∈([(0,-1),(1,-1),(-1,1),(0,1)] : List Cell)) :
    BrickNear 4 center (Cell.add other delta) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> dsimp [BrickNear,Cell.add] at near ⊢ <;> omega

/-- A nine-by-nine block of preplaced bricks guards every possible owner of
an arbitrary completion tile touching this brick's connectors. -/
theorem brickInterface_of_prefill (palette : Cell → Fin 24) (locations : List Cell)
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (retained : prescribed palette locations⊆completed) (location : Cell)
    (neighborhood : ∀ other,BrickNear 4 location other → other∈locations) :
    BrickInterface palette completed location := by
  have smaller (other : Cell) (near : BrickNear 3 location other) : other∈locations :=
    neighborhood other (by dsimp [BrickNear] at near ⊢; omega)
  have barriers (other : Cell) (near : BrickNear 3 location other)
      (entry : Atom × Cell) (he : entry∈layout (palette other)) :
      BarrierRetained palette completed other entry := by
    exact barrier_retained palette locations retained (smaller other near) he
  have selfNear : BrickNear 3 location location := by dsimp [BrickNear]; omega
  apply brickInterface_of_guards h location
    (barriers location selfNear)
    (fun entry he => own_retained palette locations retained (smaller location selfNear) he)
  intro entry he p hp right f hf covers
  have shape := (h.tilesInside f hf).1
  obtain ⟨d,hd,interior⟩ := footprint_interior_cell shape
  obtain ⟨other,atom,member,inside⟩ := global_regions_cover palette d
  have otherBounds := regionAt_bounds palette other member inside
  have hereBounds := portal_brick_bounds palette location he hp right
  have distance := Gadget.Tromino.IsFootprint.coordinate_bounds shape hd covers
  have near : BrickNear 3 location other := by
    dsimp [BrickNear,origin] at otherBounds hereBounds ⊢
    omega
  refine ⟨other,atom,member,completed_tile_contained palette other member h
    (barriers other near atom member) hf (c := Cell.sub d (atomOffset other atom)) ?_ ?_⟩
  · obtain ⟨c,hc,eq⟩ := Finset.mem_image.mp inside
    have cancel : Cell.sub d (atomOffset other atom)=c := by
      rw [← eq]
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    rw [cancel]
    exact Finset.mem_sdiff.mpr ⟨hc,fun boundary => interior
      (translated_boundary_port palette other member (Finset.mem_image.mpr ⟨c,boundary,eq⟩))⟩
  · have cancel : Cell.add (atomOffset other atom) (Cell.sub d (atomOffset other atom))=d := by
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    rwa [cancel]
end LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
