/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteFunctionTable

/-! # Correctness of finite lookup chains -/

noncomputable section

namespace LeanTrominoes
namespace Computability

theorem finiteFunctionTable_eq_of_mem
    {Alpha Beta : Type*} [DecidableEq Alpha]
    (function : Alpha → Beta) (fallback : Beta)
    {values : List Alpha} {input : Alpha}
    (member : input ∈ values) :
    finiteFunctionTable function fallback values input = function input := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      by_cases equal : input = head
      · simp [finiteFunctionTable, equal]
      · have tailMember : input ∈ tail := by
          simpa [equal] using member
        simp [finiteFunctionTable, equal, induction tailMember]

end Computability
end LeanTrominoes
