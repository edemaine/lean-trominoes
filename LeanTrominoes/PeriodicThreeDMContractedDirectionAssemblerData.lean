/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestDelimitedReversalCompiler

/-! # Role-tagged incidence words for contracted route assembly -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace ContractedDirectionAssembler

open NormalizationDirectionRequest.Batch

/-- A contracted edge contains either one retained incidence, or a forward
first incidence followed by a backward second incidence. -/
inductive Role
  | retained
  | throughFirst
  | throughSecond
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- Finite source alphabet for independently delimited incidence words. -/
inductive Token
  | role (value : Role)
  | direction (value : AxisDirection)
  | incidenceEnd
  deriving DecidableEq, Fintype, Inhabited, Repr

def isEnd : Token → Bool
  | .incidenceEnd => true
  | _ => false

def directionBlock : Token → List AxisDirection
  | .direction direction => [direction]
  | _ => []

def directions (tokens : List Token) : List AxisDirection :=
  tokens.flatMap directionBlock

def selectedRole (tokens : List Token) : Role :=
  match tokens.head? with
  | some (.role role) => role
  | _ => .retained

/-- One role-tagged incidence contributes either a complete retained edge, a
nonterminal through prefix, or a reversed complete through suffix. -/
def blockOutput (tokens : List Token) : List NormalizedToken :=
  match selectedRole tokens with
  | .retained =>
      DelimitedReversal.routeBlock (directions tokens)
  | .throughFirst =>
      (directions tokens).map .direction
  | .throughSecond =>
      DelimitedReversal.routeBlock
        (Gadget.reverseDirections (directions tokens))

def roleBlock (role : Role) (word : List AxisDirection) : List Token :=
  .role role :: word.map .direction ++ [.incidenceEnd]

@[simp] theorem directions_roleBlock
    (role : Role) (word : List AxisDirection) :
    directions (roleBlock role word) = word := by
  simp [directions, roleBlock, directionBlock, List.flatMap_map]

@[simp] theorem selectedRole_roleBlock
    (role : Role) (word : List AxisDirection) :
    selectedRole (roleBlock role word) = role := by
  rfl

@[simp] theorem blockOutput_retained
    (word : List AxisDirection) :
    blockOutput (roleBlock .retained word) =
      DelimitedReversal.routeBlock word := by
  simp [blockOutput]

@[simp] theorem blockOutput_throughFirst
    (word : List AxisDirection) :
    blockOutput (roleBlock .throughFirst word) =
      word.map NormalizedToken.direction := by
  simp [blockOutput]

@[simp] theorem blockOutput_throughSecond
    (word : List AxisDirection) :
    blockOutput (roleBlock .throughSecond word) =
      DelimitedReversal.routeBlock
        (Gadget.reverseDirections word) := by
  simp [blockOutput]

/-- Materialized incidence words before their finite role-driven assembly. -/
inductive EdgeBlock
  | retained (route : List AxisDirection)
  | through (first second : List AxisDirection)
  deriving DecidableEq

def EdgeBlock.directions : EdgeBlock → List AxisDirection
  | .retained route => route
  | .through first second =>
      first ++ Gadget.reverseDirections second

def EdgeBlock.inputTokens : EdgeBlock → List Token
  | .retained route => roleBlock .retained route
  | .through first second =>
      roleBlock .throughFirst first ++
        roleBlock .throughSecond second

def inputTokens (blocks : List EdgeBlock) : List Token :=
  blocks.flatMap EdgeBlock.inputTokens

def outputTokens (blocks : List EdgeBlock) : List NormalizedToken :=
  blocks.flatMap fun block =>
    DelimitedReversal.routeBlock block.directions

end ContractedDirectionAssembler
end PeriodicThreeDM
end LeanTrominoes
