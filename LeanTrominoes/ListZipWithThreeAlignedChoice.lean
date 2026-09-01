/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Zip

/-! # Aligned conditional choice in a three-list zip -/

namespace List

/-- An aligned control may replace a successor by the current key exactly
where the semantic successor is already fixed. -/
theorem zipWith3_choose_eq_map
    {Control Key Marker : Type*} [DecidableEq Marker]
    (project : Control → Marker) (semantic : Key → Marker)
    (marker : Marker) (next : Key → Key)
    (controls : List Control) (keys : List Key)
    (aligned : controls.map project = keys.map semantic)
    (fixed : ∀ key ∈ keys, semantic key = marker → next key = key) :
    List.zipWith3
        (fun control key successor =>
          if project control = marker then key else successor)
        controls keys (keys.map next) =
      keys.map next := by
  induction keys generalizing controls with
  | nil =>
      have controlsNil : controls = [] := by
        simpa using congrArg List.length aligned
      subst controls
      rfl
  | cons key keys induction =>
      cases controls with
      | nil => simp at aligned
      | cons control controls =>
          have headEq : project control = semantic key :=
            (List.cons.inj aligned).1
          have tailEq : controls.map project = keys.map semantic :=
            (List.cons.inj aligned).2
          have tailFixed :
              ∀ item ∈ keys, semantic item = marker → next item = item := by
            intro item itemMember itemMarker
            exact fixed item (by simp [itemMember]) itemMarker
          by_cases semanticMarker : semantic key = marker
          · have projectMarker : project control = marker :=
              headEq.trans semanticMarker
            have nextFixed : next key = key :=
              fixed key (by simp) semanticMarker
            simp only [List.map_cons, List.zipWith3]
            rw [if_pos projectMarker, nextFixed,
              induction controls tailEq tailFixed]
          · have projectNotMarker : project control ≠ marker := by
              intro projectMarker
              exact semanticMarker (headEq.symm.trans projectMarker)
            simp only [List.map_cons, List.zipWith3]
            rw [if_neg projectNotMarker,
              induction controls tailEq tailFixed]

end List
