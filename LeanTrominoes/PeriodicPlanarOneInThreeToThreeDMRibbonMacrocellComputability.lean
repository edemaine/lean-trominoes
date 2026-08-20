/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteDomainComputability
import LeanTrominoes.AxisDirectionComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocells
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerComputability

/-! # Computability of ribbon macrocell routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- The route shape inside one macrocell is a fixed finite table. -/
theorem standardRibbonMacrocellRoute_primrec :
    Primrec
      (fun input : AxisDirection × (AxisDirection × WireColor) =>
        standardRibbonMacrocellRoute input.1 input.2.1 input.2.2) :=
  Computability.finiteDomain_primrec _

/-- The local exit point is another fixed finite table. -/
theorem standardRibbonMacrocellExit_primrec :
    Primrec
      (fun input : AxisDirection × WireColor =>
        standardRibbonMacrocellExit input.1 input.2) :=
  Computability.finiteDomain_primrec _

/-- Refined macrocell origins are primitive recursive. -/
theorem ribbonMacrocellOrigin_primrec :
    Primrec ribbonMacrocellOrigin := by
  exact (Computability.cell_scale_primrec.comp
    (Primrec.const (standardThreeStrandLayout.factor : Int))
    Primrec.id).of_eq fun _ => rfl

/-- A translated macrocell exit is primitive recursive. -/
theorem ribbonMacrocellExit_primrec :
    Primrec
      (fun input : Cell × (AxisDirection × WireColor) =>
        ribbonMacrocellExit input.1 input.2.1 input.2.2) := by
  exact Computability.cell_add_primrec.comp
    (ribbonMacrocellOrigin_primrec.comp Primrec.fst)
    (standardRibbonMacrocellExit_primrec.comp Primrec.snd)

private abbrev RibbonMacrocellRouteInput :=
  Cell × (AxisDirection × (AxisDirection × WireColor))

/-- Translating a finite macrocell route to an arbitrary source cell is
primitive recursive. -/
theorem ribbonMacrocellRoute_primrec :
    Primrec
      (fun input : RibbonMacrocellRouteInput =>
        ribbonMacrocellRoute input.1 input.2.1 input.2.2.1 input.2.2.2) := by
  have shape : Primrec fun input : RibbonMacrocellRouteInput =>
      standardRibbonMacrocellRoute input.2.1 input.2.2.1 input.2.2.2 :=
    standardRibbonMacrocellRoute_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
  have addOrigin : Primrec₂ fun
      (input : RibbonMacrocellRouteInput) (point : Cell) =>
      Cell.add (ribbonMacrocellOrigin input.1) point := by
    exact Computability.cell_add_primrec.comp
      (ribbonMacrocellOrigin_primrec.comp
        (Primrec.fst.comp Primrec.fst))
      Primrec.snd
  exact (Primrec.list_map shape addOrigin).of_eq fun _ => rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
