/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripFlatEncodingSize

/-!
# Monotonicity of the rectangular strip encoding budget
-/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationCompiler

theorem stripFlatEncodingBudget_monotone :
    Monotone stripFlatEncodingBudget := by
  intro first second less
  unfold stripFlatEncodingBudget
  dsimp only
  gcongr

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
