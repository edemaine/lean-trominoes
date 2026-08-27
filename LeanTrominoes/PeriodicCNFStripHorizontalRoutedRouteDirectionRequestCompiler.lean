/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.GadgetSparseRouteDirectionReversalCompiler
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteDirectionRequestData
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for horizontal routed source-direction requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteDirectionRequest

open Computability Turing
open Gadget PeriodicOrthocrossing

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- Intermediate alphabet separating a polarity marker from expanded source
directions. -/
inductive ExpandedToken
  | operation (value : Operation)
  | direction (value : AxisDirection)
  deriving DecidableEq, Fintype

instance : Inhabited ExpandedToken := ⟨.operation .compatible⟩

def expansionBlock : Token → List ExpandedToken
  | .operation operation => [.operation operation]
  | .local query =>
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalDirectionBlock
        query).map .direction
  | .inherited query =>
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalExtendedDirectionBlock
        query).map .direction
  | .tailDirection direction =>
      List.replicate 144 (.direction direction)

def expanded (input : List Token) : List ExpandedToken :=
  input.flatMap expansionBlock

@[simp] theorem expanded_nil : expanded [] = [] := rfl

@[simp] theorem expanded_cons (token : Token) (input : List Token) :
    expanded (token :: input) = expansionBlock token ++ expanded input :=
  rfl

private theorem expanded_tailDirections (directions : List AxisDirection) :
    expanded (directions.map Token.tailDirection) =
      (repeatDirections 144 directions).map ExpandedToken.direction := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change List.replicate 144 (.direction direction) ++
          expanded (directions.map Token.tailDirection) =
        (List.replicate 144 direction ++
          repeatDirections 144 directions).map ExpandedToken.direction
      rw [induction, List.map_append]
      rfl

@[simp] theorem expanded_sourceTokens
    (source : RetainedFigureNineRouteDirectionBlock) :
    expanded (sourceTokens source) =
      source.directions.map ExpandedToken.direction := by
  cases source with
  | «local» query =>
      simp [sourceTokens, expansionBlock,
        RetainedFigureNineRouteDirectionBlock.directions]
  | inherited query directions =>
      rw [sourceTokens, expanded_cons, expansionBlock,
        expanded_tailDirections]
      simp only [RetainedFigureNineRouteDirectionBlock.directions,
        List.map_append]

@[simp] theorem expanded_tokens
    (block : HorizontalRoutedRouteDirectionBlock) :
    expanded (tokens block) =
      match block with
      | .compatible source =>
          .operation .compatible :: source.directions.map .direction
      | .incompatible source =>
          .operation .incompatible :: source.directions.map .direction
      | .complementFresh source =>
          .operation .complementFresh :: source.directions.map .direction
      | .complementOriginal source =>
          .operation .complementOriginal :: source.directions.map .direction := by
  cases block <;>
    simp [tokens, expansionBlock, expanded_sourceTokens]

noncomputable def expandedComputableInPolyTime :
    TM2ComputableInPolyTime id id expanded := by
  change TM2ComputableInPolyTime id id
    (fun input : List Token => input.flatMap expansionBlock)
  exact FiniteBlockTransducer.computableInPolyTime expansionBlock

/-- Finite control for applying a polarity stream operation. -/
structure State where
  operation : Operation
  seenDirection : Bool
  deriving DecidableEq, Fintype

instance : Inhabited State := ⟨⟨default, false⟩⟩

def initial : State := ⟨default, false⟩

def transition (state : State) : ExpandedToken →
    State × List AxisDirection
  | .operation operation => (⟨operation, false⟩, [])
  | .direction direction =>
      (⟨state.operation, true⟩,
        match state.operation with
        | .compatible => List.replicate 3 direction
        | .incompatible =>
            if state.seenDirection then [] else [direction]
        | .complementFresh =>
            if state.seenDirection then [] else [direction.opposite]
        | .complementOriginal =>
            if state.seenDirection then List.replicate 3 direction
            else [direction])

def finish (_ : State) : List AxisDirection := []

def polarityOutput (input : List ExpandedToken) : List AxisDirection :=
  FiniteStateTransducer.output initial transition finish input

private theorem scan_seen
    (operation : Operation) (directions : List AxisDirection) :
    (FiniteStateTransducer.scan transition ⟨operation, true⟩
      (directions.map ExpandedToken.direction)).2 =
      match operation with
      | .compatible | .complementOriginal => repeatDirections 3 directions
      | .incompatible | .complementFresh => [] := by
  induction directions with
  | nil => cases operation <;> rfl
  | cons direction directions induction =>
      cases operation <;>
        simp [FiniteStateTransducer.scan, transition, repeatDirections,
          induction]

@[simp] theorem polarityOutput_operation_directions
    (operation : Operation) (directions : List AxisDirection) :
    polarityOutput
        (.operation operation :: directions.map .direction) =
      operation.apply directions := by
  cases directions with
  | nil =>
      cases operation <;>
        simp [polarityOutput, FiniteStateTransducer.output,
          FiniteStateTransducer.scan, transition, finish, Operation.apply,
          repeatDirections, reverseDirections]
  | cons direction directions =>
      cases operation <;>
        simp [polarityOutput, FiniteStateTransducer.output,
          FiniteStateTransducer.scan, transition, finish, Operation.apply,
          repeatDirections, reverseDirections, scan_seen]

noncomputable def polarityOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id polarityOutput :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

/-- Complete mathematical output after horizontal doubling and reversal. -/
def output (input : List Token) : List AxisDirection :=
  reverseDirections (repeatDirections 2 (polarityOutput (expanded input)))

/-- A compact routed request emits exactly its horizontal variable-to-clause
source direction word. -/
@[simp] theorem output_tokens
    (block : HorizontalRoutedRouteDirectionBlock) :
    output (tokens block) = horizontalOccurrenceSourceDirections block := by
  unfold output horizontalOccurrenceSourceDirections
  rw [expanded_tokens]
  cases block <;> rw [polarityOutput_operation_directions] <;> rfl

/-- Finite expansion, polarity selection, doubling, and dynamic reversal form
one polynomial-time compiler. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  let expandedCompiler := expandedComputableInPolyTime
  let polarityCompiler := TM2CompositionMachine.computableInPolyTime
    expandedCompiler polarityOutputComputableInPolyTime
  let doubled := TM2CompositionMachine.computableInPolyTime polarityCompiler
    (repeatDirectionsComputableInPolyTime 2)
  let reversed := TM2CompositionMachine.computableInPolyTime doubled
    reverseDirectionsComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => reverseDirections
      (repeatDirections 2 (polarityOutput (expanded input))))
  exact reversed

end HorizontalRoutedRouteDirectionRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
