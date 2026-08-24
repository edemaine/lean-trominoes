/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

/-! # Fixed candidate blocks activated by Boolean predicates -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*}

/-- One value template in a fixed predicate-indexed block.  The second field
is its support bit whenever the containing predicate is active. -/
structure Template (Value : Type*) where
  value : Value
  supported : Bool
  deriving DecidableEq, Repr

/-- Activate a fixed template, representing an inactive slot by `none`. -/
def Template.activate (active : Bool) (template : Template Value) :
    Candidate Value where
  value := if active then some template.value else none
  supported := active && template.supported

/-- Fixed slots obtained by aligning one activation bit with each template
block.  Unequal malformed inputs stop at the shorter list. -/
def candidates : List Bool → List (List (Template Value)) →
    List (Candidate Value)
  | active :: actives, block :: blocks =>
      block.map (Template.activate active) ++ candidates actives blocks
  | _, _ => []

/-- Compact active-value output of the same aligned block family. -/
def activeValues : List Bool → List (List (Template Value)) → List Value
  | active :: actives, block :: blocks =>
      (if active then block.map Template.value else []) ++
        activeValues actives blocks
  | _, _ => []

/-- Every fixed template carries the correct base-membership support bit. -/
def CorrectTemplates [DecidableEq Value]
    (base : List Value) (blocks : List (List (Template Value))) : Prop :=
  ∀ template ∈ blocks.flatten,
    template.supported = decide (template.value ∈ base)

/-- Only active blocks need semantically correct support tags; inactive
blocks are represented by rejected `none` slots regardless of their fixed
template payloads. -/
def CorrectActiveTemplates [DecidableEq Value]
    (base : List Value) : List Bool →
      List (List (Template Value)) → Prop
  | active :: actives, block :: blocks =>
      (if active then
          ∀ template ∈ block,
            template.supported = decide (template.value ∈ base)
        else True) ∧
        CorrectActiveTemplates base actives blocks
  | _, _ => True

end LeanTrominoes.PaddedSupportedCandidateBlocks
