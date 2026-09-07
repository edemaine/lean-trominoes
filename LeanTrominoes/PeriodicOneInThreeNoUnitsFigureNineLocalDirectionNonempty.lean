/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionCompiler

/-! # Nonempty finite Figure 9 direction prefixes -/

namespace LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine

/-- Every selected template incidence contains at least one unit edge. -/
theorem normalizedLocalDirectionBlock_ne_nil :
    ∀ query : LocalDirectionQuery, normalizedLocalDirectionBlock query ≠ [] := by
  native_decide

private theorem extendedDirectionBlock_ne_nil :
    ∀ (query : LocalDirectionQuery) (direction : AxisDirection) (slot : Fin 3),
      normalizedLocalExtendedDirectionBlock
        ⟨query.1, query.2, ⟨0, fun _ => direction⟩, slot⟩ ≠ [] := by
  native_decide

/-- An extended connector cannot remove the local incidence's first edge.
Only the selected fan direction affects this finite check. -/
theorem normalizedLocalExtendedDirectionBlock_ne_nil
    (query : LocalExtendedDirectionQuery) :
    normalizedLocalExtendedDirectionBlock query ≠ [] := by
  rcases query with ⟨profile, incidence, fan, slot⟩
  simpa only [normalizedLocalExtendedDirectionBlock,
    ComposedClauseExitFanData.extendedRoute, ComposedClauseExitFanData.route]
    using extendedDirectionBlock_ne_nil
      ⟨profile, incidence⟩ (fan.direction slot) slot

end LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine
