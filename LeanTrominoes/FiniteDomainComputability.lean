/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteFunctionTableCorrectness

/-! # Primitive recursion on finite domains -/

noncomputable section

namespace LeanTrominoes
namespace Computability

/-- Every function out of a finite primitive-codable type is primitive
recursive.  Its graph is represented by the fixed table `Finset.univ`. -/
theorem finiteDomain_primrec
    {Alpha Beta : Type*}
    [Primcodable Alpha] [Primcodable Beta]
    [Fintype Alpha] [DecidableEq Alpha] [Inhabited Beta]
    (function : Alpha → Beta) :
    Primrec function := by
  let values : List Alpha := Finset.univ.toList
  exact
    (finiteFunctionTable_primrec function default values).of_eq
      fun input =>
        finiteFunctionTable_eq_of_mem function default
          (by simp [values])

end Computability
end LeanTrominoes
