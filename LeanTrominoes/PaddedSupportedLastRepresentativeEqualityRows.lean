/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SupportedLastRepresentativeEqualityRows

/-! # Fixed-slot support-guarded representative rows -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- One fixed candidate slot.  `none` denotes an inactive slot, while the
support bit records whether an active value belongs to the distinguished
base family. -/
structure Candidate (Value : Type*) where
  value : Option Value
  supported : Bool
  deriving DecidableEq, Repr

/-- The option-valued presentation stream carried by fixed candidate slots. -/
def values (candidates : List (Candidate Value)) : List (Option Value) :=
  candidates.map Candidate.value

/-- One option-equality row followed by the slot's rejection bit. -/
def row (candidates : List (Candidate Value))
    (candidate : Candidate Value) : List Bool :=
  LastRepresentativeEqualityRows.equalityRow
      (values candidates) candidate.value ++
    [!candidate.supported]

/-- One guarded equality row per fixed candidate slot. -/
def rows (candidates : List (Candidate Value)) :
    DelimitedBinaryWords.Input :=
  ⟨candidates.map (row candidates)⟩

/-- Apply the established last-representative selector to the fixed slots. -/
def selectedRows (candidates : List (Candidate Value)) :
    DelimitedBinaryWords.Input :=
  LastRepresentativeEqualityRows.rows (rows candidates)

/-- Every slot's support tag agrees with membership of its optional value in
the lifted base family.  In particular, inactive `none` slots are rejected. -/
def CorrectSupport (base : List Value)
    (candidates : List (Candidate Value)) : Prop :=
  ∀ candidate ∈ candidates,
    candidate.supported =
      decide (candidate.value ∈ base.map some)

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
