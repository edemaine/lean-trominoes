/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetICanonicalSelection

/-! # One trichromatic vertex bit selects a fixed finite local pattern -/
noncomputable section
namespace LeanTrominoes.Gadget.CanonicalISelection

def trichromaticPattern (order : TrichromaticOrder) (bit : Bool) : Finset (Placement Unit) :=
  pattern (.trichromaticVertex order) (fun _ => bit)

theorem trichromaticPattern_exact (order : TrichromaticOrder) (bit : Bool) :
    trichromaticPattern order bit ∈ exactCellTilings .I (.trichromaticVertex order) :=
  pattern_exact _ _ ⟨rfl,rfl⟩

theorem trichromaticPattern_readout (order : TrichromaticOrder) (bit : Bool) :
    iConfigurationInward (.trichromaticVertex order)
      (portConfiguration .I (orthogonalCellGadget .I (.trichromaticVertex order))
        (trichromaticPattern order bit)) .north = bit := by
  rw [trichromaticPattern,pattern_ports]
  have active : ((OrthogonalCellType.trichromaticVertex order).portColor .north).isSome := by
    cases order <;> rfl
  simpa only [PreferredISelection.profile,if_pos active] using
    (PreferredISelection.pattern_spec (.trichromaticVertex order) (fun _ => bit) ⟨rfl,rfl⟩).2.2 .north active

theorem trichromaticPattern_eq (order : TrichromaticOrder) (inward : Side → Bool)
    (valid : PeriodicOrthogonalDrawing.satisfiesOrientation (.trichromaticVertex order) inward)
    (bit : Bool) (pin : inward .north = bit) :
    pattern (.trichromaticVertex order) inward = trichromaticPattern order bit := by
  apply pattern_eq_of_active_eq
  intro side active
  change inward .west = inward .north ∧ inward .north = inward .east at valid
  cases order <;> cases side <;>
    simp only [OrthogonalCellType.portColor,Option.isSome_none,Bool.false_eq_true] at active
  all_goals first | exact pin | exact valid.1.trans pin | exact valid.2.symm.trans pin

end LeanTrominoes.Gadget.CanonicalISelection
