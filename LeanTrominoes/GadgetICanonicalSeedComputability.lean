/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetICanonicalSeedTiling

/-! # Primitive-recursive emission of canonical finite vertex patterns -/
noncomputable section
namespace LeanTrominoes.Gadget.CanonicalISelection
open Computability TrominoAssignment
attribute [local irreducible] trichromaticPattern

theorem translatePlacement_primrec : Primrec₂ translatePlacement := by
  have constructor : Primrec placementUnitEquiv.symm := Primrec.of_equiv_symm
  exact constructor.comp (Primrec.pair (Primrec.const ())
    (Primrec.pair (placement_symmetry_primrec.comp Primrec.snd)
      (cell_add_primrec.comp Primrec.fst (placement_offset_primrec.comp Primrec.snd))))

theorem latticeBlockOrigin_primrec : Primrec latticeBlockOrigin :=
  (cell_scale_primrec.comp (Primrec.const 6) Primrec.id).of_eq (fun _ => rfl)

theorem seedPlacements_primrec : Primrec seedPlacements := by
  have patterns : Primrec (fun p : TrichromaticOrder × Bool => (trichromaticPattern p.1 p.2).toList) :=
    Primrec.dom_finite _
  have one : Primrec (fun pin : (Cell × TrichromaticOrder) × Bool =>
      (trichromaticPattern pin.1.2 pin.2).toList.map (translatePlacement (latticeBlockOrigin pin.1.1))) :=
    Primrec.list_map
      (patterns.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (translatePlacement_primrec.comp
        (latticeBlockOrigin_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
  exact Primrec.list_flatMap Primrec.id (one.comp Primrec.snd)

theorem refinedSeedPlacements_primrec : Primrec (fun seed : VertexSeed =>
    (seedPlacements seed).map PlusRefinement.expandPlacement) :=
  PlusRefinement.seed_refinement_primrec.comp seedPlacements_primrec

end LeanTrominoes.Gadget.CanonicalISelection
