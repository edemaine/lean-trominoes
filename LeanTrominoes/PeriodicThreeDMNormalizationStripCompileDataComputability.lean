/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCellTypesComputability

/-! # Computability of rectangular drawing compiler data -/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem compiledStripCellTypes_primrec :
    Primrec compiledStripCellTypes :=
  finalStripCellTypes_primrec

theorem compileStripData_primrec : Primrec compileStripData := by
  have horizontalPeriodPred : Primrec fun input : Input =>
      finalNormalizationPeriod input - 1 :=
    Primrec.nat_sub.comp finalNormalizationPeriod_primrec
      (Primrec.const 1)
  have verticalPeriodPred : Primrec fun input : Input =>
      3 * finalNormalizationPeriod input :=
    Primrec.nat_mul.comp (Primrec.const 3)
      finalNormalizationPeriod_primrec
  exact (Primrec.pair horizontalPeriodPred
    (Primrec.pair verticalPeriodPred
      compiledStripCellTypes_primrec)).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
