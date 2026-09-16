/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIStripBandCompiler
import LeanTrominoes.CompletionStripCapCompiler

/-! # A finite periodic strip prefill from a blank-padded brick palette -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

def compileStrip (period count : Nat) (palette : Cell → Fin 24) : PeriodicStripTrominoPrefill where
  height := 162*count+5
  period := 36*period
  motif := ((bandMotif period count palette).map fun p => p.shift (0,2)) ++
    (StripCaps.expandedCap .I true period ++
      (StripCaps.expandedCap .I false period).map fun p => p.shift (0,162*(count:Int)+2))

theorem compileStrip_prescribed (period count : Nat) (hp : 0 < period) (palette : Cell → Fin 24)
    (periodic : ∀ c (i : Int), palette (c.1+i*period,c.2) = palette c) :
    (compileStrip period count palette).periodic.prescribed .I =
      (fun f => f.image (Cell.add (0,2))) ''
        (bandPrescribed palette count ∪ StripCaps.shellPrefill .I (162*count)) := by
  rw [HorizontalPrefill.strip_prescribed]
  have top := StripCaps.expandedCap_prescribed .I true period hp
  have bottom := StripCaps.expandedCap_prescribed .I false period hp
  change HorizontalPrefill.prescribed .I (36*(period:Int)) _ = _ at top bottom
  change HorizontalPrefill.prescribed .I (36*(period:Int)) _ = _
  simp only [compileStrip,HorizontalPrefill.prescribed_append,HorizontalPrefill.prescribed_shift,
    bandMotif_prescribed period count hp palette periodic,top,bottom]
  simp [StripCaps.shellPrefill,Set.image_union,Set.image_image,Finset.image_image,
    Function.comp_def,Cell.add,Int.add_assoc,Int.add_comm,Int.add_left_comm]
  have vertical (k : Int) : Cell.add (0,k) = fun x => (x.1,x.2+k) := by
    funext x
    simp [Cell.add,Int.add_comm]
  simp only [vertical]

theorem compileStrip_region (period count : Nat) (palette : Cell → Fin 24) :
    (compileStrip period count palette).region =
      Cell.add (0,2) '' StripCaps.cappedRegion (162*(count:Int)) := by
  ext c
  rw [StripCaps.mem_translate_iff]
  simp [PeriodicStripTrominoPrefill.region,compileStrip,StripCaps.cappedRegion,Cell.sub]
  omega

/-- Semantic correctness of the actual finite strip-completion input. -/
theorem compileStrip_correct (period count : Nat) (hp : 0 < period) (hn : 0 < count)
    (palette : Cell → Fin 24)
    (periodic : ∀ c (i : Int), palette (c.1+i*period,c.2) = palette c)
    (blank : ∀ location, location.2 ≤ 0 ∨ (count:Int) ≤ location.2 → palette location = 0) :
    PeriodicStripTrominoPrefill.problem .I (compileStrip period count palette) ↔
      Tromino.I.Completable Set.univ (globalPrescribed palette) := by
  unfold PeriodicStripTrominoPrefill.problem
  rw [compileStrip_prescribed period count hp palette periodic,compileStrip_region,
    Tromino.completable_translate_iff,capped_strip_iff_plane palette count (by exact_mod_cast hn) blank]
  have hh : 0 < (compileStrip period count palette).height := by simp [compileStrip]
  have ph : 0 < (compileStrip period count palette).period := by simp [compileStrip,hp]
  simp only [hh,ph,true_and]

end LeanTrominoes.CompletionPattern.IBricks
