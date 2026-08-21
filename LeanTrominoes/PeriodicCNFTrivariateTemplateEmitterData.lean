/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramTokens

/-! # Trivariate affine token templates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace TrivariateTemplateEmitter

open UnaryProgramTokens

/-- One finite recipe whose unary run is affine in two global dimensions and
one zero-based output position. -/
inductive Recipe
  | fixed (token : Token)
  | atom (base firstStride secondStride positionStride : Nat)
  deriving DecidableEq

namespace Recipe

/-- Token block contributed by one recipe at concrete counter values. -/
def tokens (first second position : Nat) : Recipe → List Token
  | .fixed token => [token]
  | .atom base firstStride secondStride positionStride =>
      List.replicate
        (base + firstStride * first + secondStride * second +
          positionStride * position)
        .atomUnit

end Recipe

/-- Complete fixed recipe at one output position. -/
def positionTokens (recipes : List Recipe)
    (first second position : Nat) : List Token :=
  recipes.flatMap (Recipe.tokens first second position)

/-- Consecutive trivariate templates beginning at `firstPosition`. -/
def positionRangeTokens (recipes : List Recipe)
    (first second firstPosition : Nat) : Nat → List Token
  | 0 => []
  | count + 1 =>
      positionTokens recipes first second firstPosition ++
        positionRangeTokens recipes first second (firstPosition + 1) count

@[simp] theorem positionRangeTokens_zero (recipes : List Recipe)
    (first second firstPosition : Nat) :
    positionRangeTokens recipes first second firstPosition 0 = [] :=
  rfl

theorem positionRangeTokens_succ (recipes : List Recipe)
    (first second firstPosition count : Nat) :
    positionRangeTokens recipes first second firstPosition (count + 1) =
      positionTokens recipes first second firstPosition ++
        positionRangeTokens recipes first second (firstPosition + 1) count :=
  rfl

/-- Semantic output of the future finite machine: retain the workspace and
append the exact trivariate template range followed by a fixed suffix. -/
def appendedOutput {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Data ⊕ Token)) : List (Data ⊕ Token) :=
  let selectedCount (selected : Data → Bool) :=
    UnaryPolynomialPaddingMachine.selectedCount
      (fun item => match item with
        | .inl data => selected data
        | .inr _ => false)
      workspace
  workspace ++
    (positionRangeTokens recipes
        (selectedCount firstSelected)
        (selectedCount secondSelected) 0
        (selectedCount positionSelected) ++ ending).map Sum.inr

end TrivariateTemplateEmitter
end PeriodicCNF
end LeanTrominoes
