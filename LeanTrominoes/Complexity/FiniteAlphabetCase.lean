/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.Fintype.Basic

/-! # Empty/nonempty case selection for finite alphabets -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetCase

universe u v

/-- Select data constructed separately for the empty and nonempty cases of a
finite type.  Packaging the choice at an abstract result type prevents large
compiler records from being reduced during case analysis. -/
noncomputable def choose
    {Symbol : Type u} {Result : Type v} [Fintype Symbol]
    (emptyCase : IsEmpty Symbol → Result)
    (nonemptyCase : Nonempty Symbol → Result) : Result := by
  classical
  apply Classical.choice
  cases isEmpty_or_nonempty Symbol with
  | inl empty => exact ⟨emptyCase empty⟩
  | inr nonempty => exact ⟨nonemptyCase nonempty⟩

end LeanTrominoes.FiniteAlphabetCase

end
