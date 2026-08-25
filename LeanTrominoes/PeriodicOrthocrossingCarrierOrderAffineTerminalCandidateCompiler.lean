/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressionBatchCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateRecipeActivationCompiler

/-! # Compiler for direction-split terminal order-coordinate candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing

/-- One activity bit for every direction-split terminal key recipe. -/
def terminalDirectionalExpandedActives
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  predicateListExpandedActives terminalDirectionalPredicates
    terminalDirectionalCarrierKeyRecipeBlocks tokens

def terminalDirectionalExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id terminalDirectionalExpandedActives := by
  exact predicateListExpandedActivesComputableInPolyTime
    terminalDirectionalPredicates
    terminalDirectionalCarrierKeyRecipeBlocks

/-- Positive or negative normalized direction-split terminal coordinates. -/
def terminalDirectionalOrderFields (keepPositive : Bool)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  normalizedFields keepPositive terminalDirectionalOrderExpressions tokens

def terminalDirectionalOrderFieldsComputableInPolyTime
    (keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (terminalDirectionalOrderFields keepPositive) := by
  exact normalizedFieldsComputableInPolyTime keepPositive
    terminalDirectionalOrderExpressions

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
