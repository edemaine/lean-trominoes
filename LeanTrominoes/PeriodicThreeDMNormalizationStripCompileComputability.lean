/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripDrawingFromDataComputability
import LeanTrominoes.PeriodicThreeDMNormalizationStripExecutableCorrectness

/-! # Computability of the rectangular drawing compiler -/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem computableCompileStrip_primrec : Primrec computableCompileStrip :=
  periodicOrthogonalStripDrawingFromData_primrec.comp
    compileStripData_primrec

theorem compileStrip_primrec : Primrec compileStrip :=
  computableCompileStrip_primrec.of_eq computableCompileStrip_eq_compileStrip

theorem compileStrip_computable : Computable compileStrip :=
  compileStrip_primrec.to_comp

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
