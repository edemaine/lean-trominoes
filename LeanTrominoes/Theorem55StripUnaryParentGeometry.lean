/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripUnaryCompiler

/-! # Exact finite parent cells for the repeated strip motif -/

namespace LeanTrominoes.Theorem55StripUnary

theorem encode_half_nonnegative (z : Int) (hz : 0 ≤ z) :
    Encodable.encode z / 2 = z.toNat := by
  cases z with
  | ofNat n => change (2*n)/2 = n; omega
  | negSucc n => omega

theorem naturalMotif_eq (source : PeriodicStrip) (valid : source.IsWellFormed) :
    naturalMotif source = source.motif.map (fun c => (c.1.toNat,c.2.toNat)) := by
  unfold naturalMotif
  apply List.map_congr_left
  intro c hc
  have bounds := valid.2.2 c hc
  rw [encode_half_nonnegative c.1 bounds.1,encode_half_nonnegative c.2 bounds.2.2.1]

theorem naturalMotif_bounds (source : PeriodicStrip) (valid : source.IsWellFormed)
    {p : Nat×Nat} (hp : p ∈ naturalMotif source) : p.1 < source.period ∧ p.2 < source.width := by
  rw [naturalMotif_eq source valid] at hp
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
  have bounds := valid.2.2 c hc
  dsimp [PeriodicStrip.InFundamentalDomain] at bounds
  constructor <;> omega

theorem naturalMotif_coe (source : PeriodicStrip) (valid : source.IsWellFormed)
    {p : Nat×Nat} (hp : p ∈ naturalMotif source) : natCell p ∈ source.motif := by
  rw [naturalMotif_eq source valid] at hp
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
  have bounds := valid.2.2 c hc
  dsimp [PeriodicStrip.InFundamentalDomain] at bounds
  have equal : natCell (c.1.toNat,c.2.toNat) = c := by
    apply Prod.ext <;> dsimp [natCell] <;> omega
  exact equal ▸ hc

theorem parentTable_rows (source : PeriodicStrip) : parentTable.rows source =
    (List.range (source.width+73)).flatMap (fun j =>
      (naturalMotif source).map (fun p => (j*source.period+p.1,p.2+10))) := by
  simp [parentTable,repetitionTable,offsets,motifTable,UnaryPointTable.sum,UnaryPointTable.sumRows,
    UnaryPointTable.line,UnaryPointTable.affine,List.flatMap_map,List.map_map,Function.comp_def]

theorem parentTable_bound (source : PeriodicStrip) (valid : source.IsWellFormed)
    {p : Nat×Nat} (hp : p ∈ parentTable.rows source) :
    p.1 < (source.width+73)*source.period ∧ 10 ≤ p.2 ∧ p.2 < source.width+10 := by
  rw [parentTable_rows] at hp
  obtain ⟨j,hj,hm⟩ := List.mem_flatMap.mp hp
  obtain ⟨p,hmotif,rfl⟩ := List.mem_map.mp hm
  have hj := List.mem_range.mp hj
  have bounds := naturalMotif_bounds source valid hmotif
  dsimp
  constructor
  · nlinarith
  · omega

theorem parentTable_shifted (source : PeriodicStrip) (valid : source.IsWellFormed)
    {p : Nat×Nat} (hp : p ∈ parentTable.rows source) : natCell p ∈ Theorem55StripSource.shifted source := by
  rw [parentTable_rows] at hp
  obtain ⟨j,hj,hm⟩ := List.mem_flatMap.mp hp
  obtain ⟨p,hmotif,rfl⟩ := List.mem_map.mp hm
  have bounds := naturalMotif_bounds source valid hmotif
  have base := naturalMotif_coe source valid hmotif
  change Cell.add (0,-10) (natCell _) ∈ source.carrier
  rw [source.mem_carrier_iff]
  refine ⟨by dsimp [Cell.add,natCell]; omega,by dsimp [Cell.add,natCell]; omega,natCell p,base,?_,?_⟩
  · simp [natCell,Cell.add]
  · refine ⟨(j : Int),?_⟩
    simp [natCell,Cell.add,Nat.cast_add,Nat.cast_mul,mul_comm]

theorem shifted_parent_exists (source : PeriodicStrip) (valid : source.IsWellFormed)
    (c : Cell) (hx₀ : 0 ≤ c.1) (hx₁ : c.1 ≤ Theorem55StripSource.period source)
    (hc : c ∈ Theorem55StripSource.shifted source) :
    ∃ p ∈ parentTable.rows source, natCell p = c := by
  change Cell.add (0,-10) c ∈ source.carrier at hc
  rw [source.mem_carrier_iff] at hc
  obtain ⟨hy₀,hy₁,base,hbase,hy,k,hk⟩ := hc
  have hb := valid.2.2 base hbase
  dsimp [Cell.add,PeriodicStrip.InFundamentalDomain] at hk hy hb hy₀ hy₁
  have hp : (0 : Int) < source.period := by exact_mod_cast valid.2.1
  have upper : c.1 ≤ ((source.width : Int)+72)*source.period := by
    simpa [Theorem55StripSource.period] using hx₁
  have k0 : 0 ≤ k := by
    by_contra bad
    have small : k ≤ -1 := by omega
    have mul := mul_le_mul_of_nonneg_left small (le_of_lt hp)
    nlinarith
  have kmax : k < (source.width : Int)+73 := by
    by_contra bad
    have large : (source.width : Int)+73 ≤ k := by omega
    have mul := mul_le_mul_of_nonneg_left large (le_of_lt hp)
    nlinarith
  have kcast : (k.toNat : Int) = k := by omega
  have bx : (base.1.toNat : Int) = base.1 := by omega
  have by' : (base.2.toNat : Int) = base.2 := by omega
  have member : (base.1.toNat,base.2.toNat) ∈ naturalMotif source := by
    rw [naturalMotif_eq source valid]
    exact List.mem_map.mpr ⟨base,hbase,rfl⟩
  refine ⟨(k.toNat*source.period+base.1.toNat,base.2.toNat+10),?_,?_⟩
  · rw [parentTable_rows]
    exact List.mem_flatMap.mpr ⟨k.toNat,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨_,member,rfl⟩⟩
  · apply Prod.ext <;> dsimp [natCell]
    · push_cast
      rw [kcast,bx]
      nlinarith
    · push_cast
      rw [by']
      omega

end LeanTrominoes.Theorem55StripUnary
