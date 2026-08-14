/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompileDataComputability

/-! # Primitive-recursive reconstruction of a rectangular drawing -/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

theorem periodicOrthogonalStripDrawingFromData_primrec :
    Primrec periodicOrthogonalStripDrawingFromData :=
  (Primrec.of_equiv_symm :
    Primrec PeriodicOrthogonalDrawing.equivData.symm).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
