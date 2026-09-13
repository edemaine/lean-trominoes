/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripUnaryCrossGeometry

/-! # Collision-free coordinate keys and exact lock removal -/

namespace LeanTrominoes.Theorem55StripUnary

theorem side_large (source : PeriodicStrip) (positive : 0 < source.period) : 216 ≤ side source := by
  have := Theorem55StripSource.period_large source positive
  dsimp [side]
  omega

theorem radix_eq (source : PeriodicStrip) : radix source = side source+3*source.period+3 := by
  unfold radix side Theorem55StripSource.period
  ring

theorem rightLockTable_rows (source : PeriodicStrip) :
    rightLockTable.rows source = rightLockOffsets.map (fun q => (side source-4+q.1,q.2)) := by
  simp [rightLockTable,UnaryPointTable.sum,UnaryPointTable.sumRows,UnaryPointTable.line,
    UnaryPointTable.constant,List.map_map,Function.comp_def]

theorem rightLockTable_image (source : PeriodicStrip) (positive : 0 < source.period) :
    ((rightLockTable.rows source).map unbias).toFinset = KeyedPeriodicComplement.horizontalLock (side source) := by
  have hn := side_large source positive
  have sub : ((side source-4 : Nat) : Int) = (side source : Int)-4 := by omega
  rw [rightLockTable_rows]
  have mapped : (rightLockOffsets.map (fun q => (side source-4+q.1,q.2))).map unbias =
      [((side source : Int)-4,2),((side source : Int)-4,3),((side source : Int)-3,3),
        ((side source : Int)-2,3),((side source : Int)-1,3)] := by
    simp [rightLockOffsets,unbias,sub,List.cons.injEq,Prod.mk.injEq]
    omega
  rw [mapped]
  simp [KeyedPeriodicComplement.horizontalLock]

theorem rightLockTable_exact (source : PeriodicStrip) (positive : 0 < source.period) (point : Nat×Nat) :
    point ∈ rightLockTable.rows source ↔ unbias point ∈ KeyedPeriodicComplement.horizontalLock (side source) := by
  rw [← rightLockTable_image source positive,List.mem_toFinset,List.mem_map]
  constructor
  · intro h; exact ⟨point,h,rfl⟩
  · rintro ⟨q,hq,he⟩
    exact unbias_injective he ▸ hq

theorem refinedPoints_bound (parents : List (Nat×Nat)) (limit : Nat)
    (bounded : ∀ p ∈ parents, p.1 < limit) {point : Nat×Nat} (hp : point ∈ refinedPoints parents) :
    point.1 < 3*limit := by
  obtain ⟨p,hparent,hm⟩ := List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
  have hb := bounded p hparent
  have hq := crossOffsets_bound hq
  dsimp
  omega

theorem holeTable_key_bound (source : PeriodicStrip) (valid : source.IsWellFormed)
    {p : Nat×Nat} (hp : p ∈ holeTable.rows source) : p.1 < radix source := by
  rw [holeTable_rows,List.mem_append] at hp
  rcases hp with hp | hp
  · have hb := refinedPoints_bound (parentTable.rows source) ((source.width+73)*source.period)
      (fun p hp => (parentTable_bound source valid hp).1) hp
    dsimp [radix]
    omega
  · have hb := refinedPoints_bound paddingParents 16 (by
      intro p hp
      simp only [paddingParents,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hp
    have large := side_large source valid.2.1
    rw [radix_eq]
    omega

theorem excludedTable_key_bound (source : PeriodicStrip) (valid : source.IsWellFormed)
    {p : Nat×Nat} (hp : p ∈ excludedTable.rows source) : p.1 < radix source := by
  change p ∈ holeTable.rows source ++ rightLockTable.rows source at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact holeTable_key_bound source valid hp
  · rw [rightLockTable_rows] at hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hq : q.1 ≤ 4 := by
      simp only [rightLockOffsets,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
    have large := side_large source valid.2.1
    rw [radix_eq]
    dsimp
    omega

theorem key_injective (source : PeriodicStrip) {p q : Nat×Nat}
    (hp : p.1 < radix source) (hq : q.1 < radix source) (he : key source p = key source q) : p = q := by
  have hx : p.1 = q.1 := by
    have h := congrArg (· % radix source) he
    simpa [key,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hq] using h
  have hy : p.2*radix source = q.2*radix source := by unfold key at he; omega
  have equalY := Nat.eq_of_mul_eq_mul_right (by omega : 0 < radix source) hy
  exact Prod.ext hx equalY

/-- No two queried coordinate pairs alias under the unary key representation. -/
theorem excludedKeys_exact (source : PeriodicStrip) (valid : source.IsWellFormed)
    (point : Nat×Nat) (inside : unbias point ∈ KeyedPeriodicComplement.square (side source)) :
    key source point ∈ excludedKeys source ↔
      unbias point ∈ Theorem55StripSource.holes source ∨
        unbias point ∈ KeyedPeriodicComplement.horizontalLock (side source) := by
  have hb := (KeyedPeriodicComplement.mem_square _ _).mp inside
  have pointBound : point.1 < radix source := by
    rw [radix_eq]
    dsimp [unbias] at hb
    omega
  have membership : key source point ∈ excludedKeys source ↔ point ∈ excludedTable.rows source := by
    rw [excludedKeys,List.mem_map]
    constructor
    · rintro ⟨q,hq,he⟩
      exact key_injective source (excludedTable_key_bound source valid hq) pointBound he ▸ hq
    · intro hp; exact ⟨point,hp,rfl⟩
  rw [membership]
  change point ∈ holeTable.rows source ++ rightLockTable.rows source ↔ _
  rw [List.mem_append,holeTable_exact source valid point inside,rightLockTable_exact source valid.2.1]

end LeanTrominoes.Theorem55StripUnary
