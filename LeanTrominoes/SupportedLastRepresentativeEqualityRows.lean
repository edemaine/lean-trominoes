/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsSemantics

/-! # Last-representative equality rows with a support guard -/

namespace LeanTrominoes.SupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- One equality row followed by a rejection bit that is true exactly when
the represented value lies outside the supported base set. -/
def row (base candidates : List Value) (value : Value) : List Bool :=
  LastRepresentativeEqualityRows.equalityRow candidates value ++
    [decide (value ∉ base)]

/-- One guarded equality row per candidate value. -/
def rows (base candidates : List Value) : DelimitedBinaryWords.Input :=
  ⟨candidates.map (row base candidates)⟩

/-- Apply the existing last-representative selector to guarded rows. -/
def selectedRows (base candidates : List Value) :
    DelimitedBinaryWords.Input :=
  LastRepresentativeEqualityRows.rows (rows base candidates)

end LeanTrominoes.SupportedLastRepresentativeEqualityRows
