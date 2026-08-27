/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteDirectionRequestData

/-! # Horizontal routed requests from finite route headers -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeader

open PeriodicCNF
open PeriodicOrthocrossing
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader

/-- Apply the finite polarity operation to one retained Figure 9 block. -/
def operationBlock (operation : Operation)
    (source : RetainedFigureNineRouteDirectionBlock) :
    HorizontalRoutedRouteDirectionBlock :=
  match operation with
  | .compatible => .compatible source
  | .incompatible => .incompatible source
  | .complementFresh => .complementFresh source
  | .complementOriginal => .complementOriginal source

/-- Complete the sole dynamic field of an inherited header with its source
tail word.  Local headers ignore the supplied tail. -/
def block (header : Header) (sourceTailDirections : List AxisDirection) :
    HorizontalRoutedRouteDirectionBlock :=
  match header.figurePrefix with
  | .local query =>
      operationBlock header.polarity.operation (.local query)
  | .inherited _ query =>
      operationBlock header.polarity.operation
        (.inherited query sourceTailDirections)

/-- The compact request prefix determined entirely by one finite header. -/
def tokens (header : Header) :
    List HorizontalRoutedRouteDirectionRequest.Token :=
  HorizontalRoutedRouteDirectionRequest.tokens (block header [])

/-- Completing an inherited header appends exactly the raw tail-direction
tokens; a local header is already complete. -/
theorem complete_tokens (header : Header)
    (sourceTailDirections : List AxisDirection) :
    HorizontalRoutedRouteDirectionRequest.tokens
        (block header sourceTailDirections) =
      tokens header ++
        match header.figurePrefix with
        | .local _ => []
        | .inherited _ _ =>
            sourceTailDirections.map
              HorizontalRoutedRouteDirectionRequest.Token.tailDirection := by
  rcases header with ⟨⟨sourceSlot, operation⟩, figurePrefix⟩
  cases figurePrefix <;> cases operation <;> rfl

/-- Concatenated finite routed-request prefixes. -/
def stream (headers : List Header) :
    List HorizontalRoutedRouteDirectionRequest.Token :=
  headers.flatMap tokens

end HorizontalRoutedRouteHeader
end PeriodicCNFStripReduction
end LeanTrominoes
