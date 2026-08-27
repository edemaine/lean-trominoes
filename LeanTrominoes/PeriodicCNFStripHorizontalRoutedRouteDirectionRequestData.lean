/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteDirectionBlock

/-! # Compact requests for horizontal routed source directions -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteDirectionRequest

open Gadget PeriodicOrthocrossing

/-- The four stream operations introduced by routed polarity normalization. -/
inductive Operation
  | compatible
  | incompatible
  | complementFresh
  | complementOriginal
  deriving DecidableEq, Fintype, Inhabited

def Operation.apply (operation : Operation)
    (directions : List AxisDirection) : List AxisDirection :=
  match operation with
  | .compatible => repeatDirections 3 directions
  | .incompatible => (repeatDirections 3 directions).take 1
  | .complementFresh =>
      reverseDirections ((repeatDirections 3 directions).drop 1 |>.take 1)
  | .complementOriginal => (repeatDirections 3 directions).drop 2

/-- Finite local data plus an optional dynamic inherited source-tail word. -/
inductive Token
  | operation (value : Operation)
  | local (query : PlanarOneInThreeNoUnitsFigureNine.LocalDirectionQuery)
  | inherited
      (query : PlanarOneInThreeNoUnitsFigureNine.LocalExtendedDirectionQuery)
  | tailDirection (value : AxisDirection)
  deriving DecidableEq, Fintype, Inhabited

def sourceTokens : RetainedFigureNineRouteDirectionBlock → List Token
  | .local query => [.local query]
  | .inherited query sourceTailDirections =>
      .inherited query :: sourceTailDirections.map .tailDirection

def tokens : HorizontalRoutedRouteDirectionBlock → List Token
  | .compatible source => .operation .compatible :: sourceTokens source
  | .incompatible source => .operation .incompatible :: sourceTokens source
  | .complementFresh source =>
      .operation .complementFresh :: sourceTokens source
  | .complementOriginal source =>
      .operation .complementOriginal :: sourceTokens source

@[simp] theorem Operation.apply_block
    (block : HorizontalRoutedRouteDirectionBlock) :
    let operation := match block with
      | .compatible _ => Operation.compatible
      | .incompatible _ => Operation.incompatible
      | .complementFresh _ => Operation.complementFresh
      | .complementOriginal _ => Operation.complementOriginal
    let source := match block with
      | .compatible source | .incompatible source |
          .complementFresh source | .complementOriginal source => source
    operation.apply source.directions =
      block.directions RetainedFigureNineRouteDirectionBlock.directions := by
  cases block <;> rfl

end HorizontalRoutedRouteDirectionRequest
end PeriodicCNFStripReduction
end LeanTrominoes
