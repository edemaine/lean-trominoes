/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentPredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineDirectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchCompiler
import LeanTrominoes.SeparatedBooleanGuardCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Guarded affine route-shape directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- Compile one affine predicate as a singleton Boolean word. -/
noncomputable def Predicate.evalTokensComputableInPolyTime
    (predicate : Predicate) :
    TM2ComputableInPolyTime id (fun value => [value])
      (predicate.evalTokens) := by
  let evaluated := predicateListTruthValuesComputableInPolyTime [predicate]
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq evaluated
    (fun tokens => by simp)

/-- Select both the diagonal descriptor pair and one matching route shape. -/
def RouteShape.diagonalDirectionGuard (shape : RouteShape) : Predicate :=
  all [carrierSegmentSameEdgeIndex, shape.guard .first]

/-- Candidate direction word contributed by one guarded affine shape. -/
def RouteShape.guardedDirectionWord
    (shape : RouteShape)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  if (shape.diagonalDirectionGuard.evalTokens tokens) then
    shape.compiledDirectionWord .first tokens
  else
    []

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- A fixed affine shape's candidate direction word is polynomial-time
computable: evaluate its guard and its dynamic word independently, then gate
the latter with the former. -/
noncomputable def RouteShape.guardedDirectionWordComputableInPolyTime
    (shape : RouteShape) :
    TM2ComputableInPolyTime id id shape.guardedDirectionWord := by
  let guard := shape.diagonalDirectionGuard.evalTokensComputableInPolyTime
  let word := shape.compiledDirectionWordComputableInPolyTime .first
  let paired := TM2ForkMachine.computableInPolyTime guard word
  let gated := TM2CompositionMachine.computableInPolyTime paired
    (SeparatedBooleanGuard.computableInPolyTime
      (Symbol := AxisDirection))
  change TM2ComputableInPolyTime id id
    (fun tokens => SeparatedBooleanGuard.guarded
      (shape.diagonalDirectionGuard.evalTokens tokens,
        shape.compiledDirectionWord .first tokens))
  exact gated

/-- On canonical input, a shape contributes precisely when the pair is
diagonal and that shape matches its descriptor. -/
@[simp] theorem RouteShape.guardedDirectionWord_descriptorPairTokens
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    shape.guardedDirectionWord (descriptorPairTokens pair) =
      if pair.1.edgeIndex = pair.2.edgeIndex ∧ shape.Matches pair.1 then
        shape.directionWord .first pair
      else
        [] := by
  by_cases sameEdge : pair.1.edgeIndex = pair.2.edgeIndex <;>
    by_cases shapeMatches : shape.Matches pair.1 <;>
      simp [RouteShape.guardedDirectionWord,
        RouteShape.diagonalDirectionGuard,
        Predicate.evalTokens_descriptorPairTokens,
        carrierSegmentSameEdgeIndex_evalPair,
        RouteShape.evalPair_guard, descriptorAt,
        sameEdge, shapeMatches]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
