/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedUniversalWangSeedHardness
import LeanTrominoes.Computability
import LeanWang.Robinson.Scaffold.PointedExtension

/-! # Finite-seed quarter-plane problems in a fixed full-plane palette

All possible corner payloads are included once. A prescribed corner fixes
the two coordinate axes; further finite prescriptions pass through the
position layer without changing the palette.
-/

namespace LeanTrominoes.FixedMachineWangSeed.PlaneExtension
open LeanWang PointedExtension

def palette (T : TileSet) : TileSet := T.flatMap (PointedExtension.tiles T)

def naturalClass (p : Nat) : AxisClass := if p = 0 then .origin else .positive

def seeds (seed : List (Nat × WangTile)) : List (Cell × WangTile) :=
  seed.map fun p => ((p.1, 0), WangTile.product
    (positionTile (naturalClass p.1) .origin) p.2)

def Completable (T : TileSet) (seed : List (Cell × WangTile)) : Prop :=
  ∃ plane : Cell → TileIn T, ValidPlaneTiling T plane ∧
    ∀ p ∈ seed, (plane p.1).1 = p.2

private structure Decoded (T : TileSet) (tile : WangTile) where
  horizontal : AxisClass
  vertical : AxisClass
  payload : WangTile
  sourceSeed : WangTile
  payload_mem : payload ∈ regionPayloads T sourceSeed horizontal vertical
  product_eq : WangTile.product (positionTile horizontal vertical) payload = tile

private theorem decoded_nonempty {T : TileSet} {tile : WangTile}
    (member : tile ∈ palette T) : Nonempty (Decoded T tile) := by
  obtain ⟨seed, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨horizontal, vertical, payload, payloadMem, productEq⟩ :=
    PointedExtension.mem_tiles_iff.mp member
  exact ⟨⟨horizontal, vertical, payload, seed, payloadMem, productEq⟩⟩

private theorem Decoded.horizontal_match {T : TileSet} {left right : WangTile}
    (a : Decoded T left) (b : Decoded T right) (matched : left.HMatches right) :
    AxisClass.Step a.horizontal b.horizontal ∧ a.vertical = b.vertical ∧
      a.payload.HMatches b.payload := by
  rw [← a.product_eq, ← b.product_eq, WangTile.HMatches_product_iff] at matched
  exact ⟨(positionTile_hMatches_iff.mp matched.1).1,
    (positionTile_hMatches_iff.mp matched.1).2, matched.2⟩

private theorem Decoded.vertical_match {T : TileSet} {lower upper : WangTile}
    (a : Decoded T lower) (b : Decoded T upper) (matched : lower.VMatches upper) :
    AxisClass.Step a.vertical b.vertical ∧ a.horizontal = b.horizontal ∧
      a.payload.VMatches b.payload := by
  rw [← a.product_eq, ← b.product_eq, WangTile.VMatches_product_iff] at matched
  exact ⟨(positionTile_vMatches_iff.mp matched.1).1,
    (positionTile_vMatches_iff.mp matched.1).2, matched.2⟩

private theorem nonnegative_step {left right : AxisClass}
    (step : AxisClass.Step left right) (nonnegative : left ≠ .negative) : right ≠ .negative := by
  cases left <;> cases right <;> simp_all [AxisClass.Step, AxisClass.before, AxisClass.after]

theorem quarter_of_plane {T : TileSet} {seed : List (Nat × WangTile)} {corner : WangTile}
    (atOrigin : (0, corner) ∈ seed) (completed : Completable (palette T) (seeds seed)) :
    SeededQuarter T seed := by
  classical
  obtain ⟨plane, valid, retained⟩ := completed
  let decoded (p : Cell) : Decoded T (plane p).1 :=
    Classical.choice (decoded_nonempty (plane p).2)
  have horizontal (p : Cell) := (decoded p).horizontal_match (decoded (p.1 + 1, p.2)) (valid.1 p)
  have vertical (p : Cell) := (decoded p).vertical_match (decoded (p.1, p.2 + 1)) (valid.2 p)
  have cornerEq := retained ((0, 0), WangTile.product (positionTile .origin .origin) corner)
    (by exact List.mem_map.mpr ⟨(0, corner), atOrigin, rfl⟩)
  have cornerPair :
      (positionTile (decoded (0, 0)).horizontal (decoded (0, 0)).vertical,
        (decoded (0, 0)).payload) = (positionTile .origin .origin, corner) := by
    apply WangTile.product_injective
    exact (decoded (0, 0)).product_eq.trans cornerEq
  have cornerClasses : ((decoded (0, 0)).horizontal, (decoded (0, 0)).vertical) =
      (.origin, .origin) := by
    apply positionTile_injective
    exact congrArg Prod.fst cornerPair
  have startH : (decoded (0, 0)).horizontal ≠ .negative := by
    have h := congrArg Prod.fst cornerClasses
    change (decoded (0, 0)).horizontal = .origin at h
    rw [h]
    simp
  have startV : (decoded (0, 0)).vertical ≠ .negative := by
    have h := congrArg Prod.snd cornerClasses
    change (decoded (0, 0)).vertical = .origin at h
    rw [h]
    simp
  have bottomH : ∀ p : Nat, (decoded (p, 0)).horizontal ≠ .negative := by
    intro p
    induction p with
    | zero => exact startH
    | succ p ih => exact nonnegative_step (by simpa using (horizontal (p, 0)).1) ih
  have leftV : ∀ q : Nat, (decoded (0, q)).vertical ≠ .negative := by
    intro q
    induction q with
    | zero => exact startV
    | succ q ih => exact nonnegative_step (by simpa using (vertical (0, q)).1) ih
  have nonnegativeH (p q : Nat) : (decoded (p, q)).horizontal ≠ .negative := by
    induction q with
    | zero => exact bottomH p
    | succ q ih =>
        have h : (decoded (p, q)).horizontal = (decoded (p, (q + 1 : Nat))).horizontal :=
          by simpa using (vertical (p, q)).2.1
        rw [← h]
        exact ih
  have nonnegativeV (p q : Nat) : (decoded (p, q)).vertical ≠ .negative := by
    induction p with
    | zero => exact leftV q
    | succ p ih =>
        have h : (decoded (p, q)).vertical = (decoded ((p + 1 : Nat), q)).vertical :=
          by simpa using (horizontal (p, q)).2.1
        rw [← h]
        exact ih
  let quarter : Nat × Nat → TileIn T := fun p =>
    ⟨(decoded (p.1, p.2)).payload, mem_source_of_mem_regionPayloads
      (nonnegativeH p.1 p.2) (nonnegativeV p.1 p.2) (decoded (p.1, p.2)).payload_mem⟩
  refine ⟨quarter, ⟨?_, ?_⟩, ?_⟩
  · intro p
    simpa [quarter] using (horizontal (p.1, p.2)).2.2
  · intro p
    simpa [quarter] using (vertical (p.1, p.2)).2.2
  · rintro ⟨p, tile⟩ member
    have pin := retained ((p, 0), WangTile.product (positionTile (naturalClass p) .origin) tile)
      (List.mem_map.mpr ⟨(p, tile), member, rfl⟩)
    have pairEq : (positionTile (decoded (p, 0)).horizontal (decoded (p, 0)).vertical,
        (decoded (p, 0)).payload) = (positionTile (naturalClass p) .origin, tile) := by
      apply WangTile.product_injective
      exact (decoded (p, 0)).product_eq.trans pin
    exact congrArg Prod.snd pairEq

def pointedBottomSeed (seed : List (Nat × WangTile)) : List (Nat × WangTile) :=
  seed.map fun p => (p.1, WangTile.product
    (positionTile (naturalClass p.1) .origin) p.2)

/-- Only the nonnegative quadrant is needed to recover the prescribed machine history. -/
theorem quarter_of_seeded_quarter {T : TileSet} {seed : List (Nat × WangTile)} {corner : WangTile}
    (atOrigin : (0, corner) ∈ seed)
    (completed : SeededQuarter (palette T) (pointedBottomSeed seed)) :
    SeededQuarter T seed := by
  classical
  obtain ⟨plane, valid, retained⟩ := completed
  let decoded (p : Nat × Nat) : Decoded T (plane p).1 :=
    Classical.choice (decoded_nonempty (plane p).2)
  have horizontal (p : Nat × Nat) := (decoded p).horizontal_match (decoded (p.1 + 1, p.2)) (valid.1 p)
  have vertical (p : Nat × Nat) := (decoded p).vertical_match (decoded (p.1, p.2 + 1)) (valid.2 p)
  have cornerEq := retained (0, WangTile.product (positionTile .origin .origin) corner)
    (by exact List.mem_map.mpr ⟨(0, corner), atOrigin, rfl⟩)
  have cornerPair :
      (positionTile (decoded (0, 0)).horizontal (decoded (0, 0)).vertical,
        (decoded (0, 0)).payload) = (positionTile .origin .origin, corner) := by
    apply WangTile.product_injective
    exact (decoded (0, 0)).product_eq.trans cornerEq
  have cornerClasses : ((decoded (0, 0)).horizontal, (decoded (0, 0)).vertical) =
      (.origin, .origin) := by
    apply positionTile_injective
    exact congrArg Prod.fst cornerPair
  have startH : (decoded (0, 0)).horizontal ≠ .negative := by
    have h := congrArg Prod.fst cornerClasses
    change (decoded (0, 0)).horizontal = .origin at h
    rw [h]
    simp
  have startV : (decoded (0, 0)).vertical ≠ .negative := by
    have h := congrArg Prod.snd cornerClasses
    change (decoded (0, 0)).vertical = .origin at h
    rw [h]
    simp
  have bottomH : ∀ p : Nat, (decoded (p, 0)).horizontal ≠ .negative := by
    intro p
    induction p with
    | zero => exact startH
    | succ p ih => exact nonnegative_step (by simpa using (horizontal (p, 0)).1) ih
  have leftV : ∀ q : Nat, (decoded (0, q)).vertical ≠ .negative := by
    intro q
    induction q with
    | zero => exact startV
    | succ q ih => exact nonnegative_step (by simpa using (vertical (0, q)).1) ih
  have nonnegativeH (p q : Nat) : (decoded (p, q)).horizontal ≠ .negative := by
    induction q with
    | zero => exact bottomH p
    | succ q ih =>
        have h : (decoded (p, q)).horizontal = (decoded (p, (q + 1 : Nat))).horizontal :=
          by simpa using (vertical (p, q)).2.1
        rw [← h]
        exact ih
  have nonnegativeV (p q : Nat) : (decoded (p, q)).vertical ≠ .negative := by
    induction p with
    | zero => exact leftV q
    | succ p ih =>
        have h : (decoded (p, q)).vertical = (decoded ((p + 1 : Nat), q)).vertical :=
          by simpa using (horizontal (p, q)).2.1
        rw [← h]
        exact ih
  let quarter : Nat × Nat → TileIn T := fun p =>
    ⟨(decoded (p.1, p.2)).payload, mem_source_of_mem_regionPayloads
      (nonnegativeH p.1 p.2) (nonnegativeV p.1 p.2) (decoded (p.1, p.2)).payload_mem⟩
  refine ⟨quarter, ⟨?_, ?_⟩, ?_⟩
  · intro p
    simpa [quarter] using (horizontal (p.1, p.2)).2.2
  · intro p
    simpa [quarter] using (vertical (p.1, p.2)).2.2
  · rintro ⟨p, tile⟩ member
    have pin := retained (p, WangTile.product (positionTile (naturalClass p) .origin) tile)
      (List.mem_map.mpr ⟨(p, tile), member, rfl⟩)
    have pairEq : (positionTile (decoded (p, 0)).horizontal (decoded (p, 0)).vertical,
        (decoded (p, 0)).payload) = (positionTile (naturalClass p) .origin, tile) := by
      apply WangTile.product_injective
      exact (decoded (p, 0)).product_eq.trans pin
    exact congrArg Prod.snd pairEq


private theorem classOfInt_natural (p : Nat) : classOfInt p = naturalClass p := by
  by_cases zero : p = 0
  · simp [zero, classOfInt, naturalClass]
  · simp [classOfInt, naturalClass, zero]

theorem plane_of_quarter {T : TileSet} {seed : List (Nat × WangTile)}
    (completed : SeededQuarter T seed) : Completable (palette T) (seeds seed) := by
  obtain ⟨quarter, valid, retained⟩ := completed
  let plane : Cell → TileIn (palette T) := fun p =>
    ⟨planeTile quarter p, List.mem_flatMap.mpr
      ⟨(quarter (0, 0)).1, (quarter (0, 0)).2, planeTile_mem_tiles quarter rfl p⟩⟩
  refine ⟨plane, ⟨?_, ?_⟩, ?_⟩
  · intro p
    change (planeTile quarter p).HMatches (planeTile quarter (p.1 + 1, p.2))
    rw [planeTile, planeTile, WangTile.HMatches_product_iff]
    exact ⟨positionTile_hMatches_iff.mpr ⟨classOfInt_step p.1, rfl⟩,
      planePayload_hMatches quarter valid p⟩
  · intro p
    change (planeTile quarter p).VMatches (planeTile quarter (p.1, p.2 + 1))
    rw [planeTile, planeTile, WangTile.VMatches_product_iff]
    exact ⟨positionTile_vMatches_iff.mpr ⟨classOfInt_step p.2, rfl⟩,
      planePayload_vMatches quarter valid p⟩
  · intro p member
    obtain ⟨⟨position, tile⟩, original, rfl⟩ := List.mem_map.mp member
    change planeTile quarter (position, 0) = _
    simp only [planeTile, planePayload, westPayload, classOfInt_natural,
      Int.natCast_nonneg, Int.toNat_natCast, Int.toNat_zero,
      show classOfInt 0 = .origin from rfl, le_refl, if_true]
    rw [retained (position, tile) original]

theorem complete_iff {T : TileSet} {seed : List (Nat × WangTile)} {corner : WangTile}
    (atOrigin : (0, corner) ∈ seed) :
    Completable (palette T) (seeds seed) ↔ SeededQuarter T seed :=
  ⟨quarter_of_plane atOrigin, plane_of_quarter⟩

end LeanTrominoes.FixedMachineWangSeed.PlaneExtension
