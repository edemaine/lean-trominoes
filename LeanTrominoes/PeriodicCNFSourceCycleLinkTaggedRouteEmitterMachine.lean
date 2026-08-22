/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInput

/-! # Finite tagged source cycle-link route emitter -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

abbrev InputSymbol := SourceCycleLinkTaggedRouteEmitter.InputSymbol
abbrev Tag := SourceCycleLinkPositionTags.Tag
abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol
abbrev OutputToken := UnaryProgramTokens.Token

local instance : Inhabited InputSymbol := ⟨.separator⟩

inductive Stack
  | input
  | tagReverse
  | tags
  | targetReverse
  | targets
  | clauseCount
  | literalCount
  | linkIndex
  | scratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive CounterStage
  | sourceVertexClause
  | sourceVertexLiteralFirst
  | sourceVertexLiteralSecond
  | sourceEdgeLiteralFirst
  | sourceEdgeLiteralSecond
  | sourceEdgeLiteralThird
  | sourceEdgeIndexLiteral
  | sourceEdgeIndexFirst
  | sourceEdgeIndexSecond
  | sourceSourceLiteral
  | sourceSourceClause
  | sourceSourceIndex
  | targetVertexClause
  | targetVertexLiteralFirst
  | targetVertexLiteralSecond
  | targetEdgeLiteralFirst
  | targetEdgeLiteralSecond
  | targetEdgeLiteralThird
  | targetEdgeIndexLiteral
  | targetEdgeIndexFirst
  | targetEdgeIndexSecond
  | targetSourceLiteral
  | targetSourceClause
  | targetSourceIndex
  | targetTargetIndex
  deriving DecidableEq, Fintype

def CounterStage.stack : CounterStage → Stack
  | .sourceVertexClause | .sourceSourceClause |
      .targetVertexClause | .targetSourceClause => .clauseCount
  | .sourceVertexLiteralFirst | .sourceVertexLiteralSecond |
      .sourceEdgeLiteralFirst | .sourceEdgeLiteralSecond |
      .sourceEdgeLiteralThird | .sourceEdgeIndexLiteral |
      .sourceSourceLiteral | .targetVertexLiteralFirst |
      .targetVertexLiteralSecond | .targetEdgeLiteralFirst |
      .targetEdgeLiteralSecond | .targetEdgeLiteralThird |
      .targetEdgeIndexLiteral | .targetSourceLiteral => .literalCount
  | .sourceEdgeIndexFirst | .sourceEdgeIndexSecond |
      .sourceSourceIndex | .targetEdgeIndexFirst |
      .targetEdgeIndexSecond | .targetSourceIndex |
      .targetTargetIndex => .linkIndex

inductive CleanupStage
  | input
  | tagReverse
  | tags
  | targetReverse
  | targets
  | clauseCount
  | literalCount
  | linkIndex
  | scratch
  | outputReverse
  deriving DecidableEq, Fintype

def CleanupStage.stack : CleanupStage → Stack
  | .input => .input
  | .tagReverse => .tagReverse
  | .tags => .tags
  | .targetReverse => .targetReverse
  | .targets => .targets
  | .clauseCount => .clauseCount
  | .literalCount => .literalCount
  | .linkIndex => .linkIndex
  | .scratch => .scratch
  | .outputReverse => .outputReverse

def CleanupStage.next : CleanupStage → Option CleanupStage
  | .input => some .tagReverse
  | .tagReverse => some .tags
  | .tags => some .targetReverse
  | .targetReverse => some .targets
  | .targets => some .clauseCount
  | .clauseCount => some .literalCount
  | .literalCount => some .linkIndex
  | .linkIndex => some .scratch
  | .scratch => some .outputReverse
  | .outputReverse => none

inductive Label
  | scanHeader
  | pushClauseUnit
  | pushTagReverse
  | scanTargetsInput
  | pushTargetReverse
  | restoreTags
  | pushTagForward
  | restoreTargets
  | pushTargetForward
  | scanLinks
  | beginSourceRecord
  | copyCounter (stage : CounterStage)
  | restoreCounter (stage : CounterStage)
  | scanTarget
  | finishSourceTarget (tag : Tag)
  | beginTargetRecord
  | finishTargetRecord (tag : Tag)
  | incrementLink
  | cleanup (stage : CleanupStage)
  | reverseOutput
  | pushOutput
  deriving Fintype

inductive State
  | cursor (tag : Tag)
  | input (tag : Tag) (symbol : Option InputSymbol)
  | tag (tag : Tag) (symbol : Option Tag)
  | unary (tag : Tag) (symbol : Option UnarySymbol)
  | unit (tag : Tag) (symbol : Option Unit)
  | output (tag : Tag) (symbol : Option OutputToken)
  deriving Fintype

abbrev Alphabet : Stack → Type
  | .input => InputSymbol
  | .tagReverse | .tags => Tag
  | .targetReverse | .targets => UnarySymbol
  | .clauseCount | .literalCount | .linkIndex | .scratch => Unit
  | .outputReverse | .output => OutputToken

def initialTag : Tag := .singleton

def cursorTag : State → Tag
  | .cursor tag | .input tag _ | .tag tag _ | .unary tag _ |
      .unit tag _ | .output tag _ => tag

def clear (state : State) : State := .cursor (cursorTag state)

def inputFromState : State → InputSymbol
  | .input _ (some symbol) => symbol
  | _ => default

def tagFromState : State → Tag
  | .tag _ (some tag) => tag
  | .input _ (some (.left (.right tag))) => tag
  | state => cursorTag state

def unaryFromState : State → UnarySymbol
  | .unary _ (some symbol) => symbol
  | .input _ (some (.right symbol)) => symbol
  | _ => .delimiter

def outputFromState : State → OutputToken
  | .output _ (some token) => token
  | _ => default

def inputIsNone : State → Bool
  | .input _ none => true
  | _ => false

def inputIsOuterSeparator : State → Bool
  | .input _ (some .separator) => true
  | _ => false

def inputIsClauseUnit : State → Bool
  | .input _ (some (.left (.left .unit))) => true
  | _ => false

def inputIsTag : State → Bool
  | .input _ (some (.left (.right _))) => true
  | _ => false

def inputIsRight : State → Bool
  | .input _ (some (.right _)) => true
  | _ => false

def tagIsNone : State → Bool
  | .tag _ none => true
  | _ => false

def unaryIsNone : State → Bool
  | .unary _ none => true
  | _ => false

def unaryIsUnit : State → Bool
  | .unary _ (some .unit) => true
  | _ => false

def unitIsNone : State → Bool
  | .unit _ none => true
  | _ => false

def outputIsNone : State → Bool
  | .output _ none => true
  | _ => false

def cleanupIsNone : State → Bool
  | .input _ none | .tag _ none | .unary _ none |
      .unit _ none | .output _ none => true
  | _ => false

def CounterStage.unit (stage : CounterStage) : Alphabet stage.stack := by
  cases stage <;> exact ()

def CleanupStage.read (stage : CleanupStage) (state : State) :
    Option (Alphabet stage.stack) → State :=
  match stage with
  | .input => fun symbol => .input (cursorTag state) symbol
  | .tagReverse | .tags => fun symbol => .tag (cursorTag state) symbol
  | .targetReverse | .targets =>
      fun symbol => .unary (cursorTag state) symbol
  | .clauseCount | .literalCount | .linkIndex | .scratch =>
      fun symbol => .unit (cursorTag state) symbol
  | .outputReverse => fun symbol => .output (cursorTag state) symbol

def pushTokens (tokens : List OutputToken)
    (next : TM2.Stmt Alphabet Label State) :
    TM2.Stmt Alphabet Label State :=
  tokens.foldr
    (fun token continuation =>
      .push .outputReverse (fun _ => token) continuation)
    next

def sourceSuffix (tag : Tag) : List OutputToken :=
  [.atomEnd] ++
    List.replicate
      (SourceCycleLinkPositionTags.sourceTargetPortRank tag) .atomUnit ++
    List.replicate 5 .atomEnd

def targetSuffix (tag : Tag) : List OutputToken :=
  [.atomUnit, .atomEnd] ++
    List.replicate
      (SourceCycleLinkPositionTags.targetTargetPortRank tag) .atomUnit ++
    List.replicate 5 .atomEnd

def afterCounter : CounterStage → TM2.Stmt Alphabet Label State
  | .sourceVertexClause =>
      .goto fun _ => .copyCounter .sourceVertexLiteralFirst
  | .sourceVertexLiteralFirst =>
      .goto fun _ => .copyCounter .sourceVertexLiteralSecond
  | .sourceVertexLiteralSecond =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .sourceEdgeLiteralFirst)
  | .sourceEdgeLiteralFirst =>
      .goto fun _ => .copyCounter .sourceEdgeLiteralSecond
  | .sourceEdgeLiteralSecond =>
      .goto fun _ => .copyCounter .sourceEdgeLiteralThird
  | .sourceEdgeLiteralThird =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .sourceEdgeIndexLiteral)
  | .sourceEdgeIndexLiteral =>
      .goto fun _ => .copyCounter .sourceEdgeIndexFirst
  | .sourceEdgeIndexFirst =>
      .goto fun _ => .copyCounter .sourceEdgeIndexSecond
  | .sourceEdgeIndexSecond =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .sourceSourceLiteral)
  | .sourceSourceLiteral =>
      .goto fun _ => .copyCounter .sourceSourceClause
  | .sourceSourceClause =>
      .goto fun _ => .copyCounter .sourceSourceIndex
  | .sourceSourceIndex =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .scanTarget)
  | .targetVertexClause =>
      .goto fun _ => .copyCounter .targetVertexLiteralFirst
  | .targetVertexLiteralFirst =>
      .goto fun _ => .copyCounter .targetVertexLiteralSecond
  | .targetVertexLiteralSecond =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .targetEdgeLiteralFirst)
  | .targetEdgeLiteralFirst =>
      .goto fun _ => .copyCounter .targetEdgeLiteralSecond
  | .targetEdgeLiteralSecond =>
      .goto fun _ => .copyCounter .targetEdgeLiteralThird
  | .targetEdgeLiteralThird =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .targetEdgeIndexLiteral)
  | .targetEdgeIndexLiteral =>
      .goto fun _ => .copyCounter .targetEdgeIndexFirst
  | .targetEdgeIndexFirst =>
      .goto fun _ => .copyCounter .targetEdgeIndexSecond
  | .targetEdgeIndexSecond =>
      .push .outputReverse (fun _ => .atomUnit)
        (.push .outputReverse (fun _ => .atomEnd)
          (.goto fun _ => .copyCounter .targetSourceLiteral))
  | .targetSourceLiteral =>
      .goto fun _ => .copyCounter .targetSourceClause
  | .targetSourceClause =>
      .goto fun _ => .copyCounter .targetSourceIndex
  | .targetSourceIndex =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .targetTargetIndex)
  | .targetTargetIndex =>
      .goto fun state => .finishTargetRecord (cursorTag state)

def afterCleanup (stage : CleanupStage) : TM2.Stmt Alphabet Label State :=
  match stage.next with
  | some next => .load clear (.goto fun _ => .cleanup next)
  | none => .load (fun _ => .cursor initialTag) .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .scanHeader =>
      .pop .input (fun state symbol => .input (cursorTag state) symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restoreTags))
          (.branch inputIsOuterSeparator
            (.load clear (.goto fun _ => .scanTargetsInput))
            (.branch inputIsClauseUnit
              (.goto fun _ => .pushClauseUnit)
              (.branch inputIsTag
                (.goto fun _ => .pushTagReverse)
                (.load clear (.goto fun _ => .scanHeader))))))
  | .pushClauseUnit =>
      .push .clauseCount (fun _ => ())
        (.load clear (.goto fun _ => .scanHeader))
  | .pushTagReverse =>
      .push .tagReverse tagFromState
        (.push .literalCount (fun _ => ())
          (.load clear (.goto fun _ => .scanHeader)))
  | .scanTargetsInput =>
      .pop .input (fun state symbol => .input (cursorTag state) symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restoreTags))
          (.branch inputIsRight
            (.goto fun _ => .pushTargetReverse)
            (.load clear (.goto fun _ => .scanTargetsInput))))
  | .pushTargetReverse =>
      .push .targetReverse unaryFromState
        (.load clear (.goto fun _ => .scanTargetsInput))
  | .restoreTags =>
      .pop .tagReverse (fun state symbol => .tag (cursorTag state) symbol)
        (.branch tagIsNone
          (.load clear (.goto fun _ => .restoreTargets))
          (.goto fun _ => .pushTagForward))
  | .pushTagForward =>
      .push .tags tagFromState
        (.load clear (.goto fun _ => .restoreTags))
  | .restoreTargets =>
      .pop .targetReverse
        (fun state symbol => .unary (cursorTag state) symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .scanLinks))
          (.goto fun _ => .pushTargetForward))
  | .pushTargetForward =>
      .push .targets unaryFromState
        (.load clear (.goto fun _ => .restoreTargets))
  | .scanLinks =>
      .pop .tags (fun state symbol => .tag (cursorTag state) symbol)
        (.branch tagIsNone
          (.load clear (.goto fun _ => .reverseOutput))
          (.load (fun state => .cursor (tagFromState state))
            (.goto fun _ => .beginSourceRecord)))
  | .beginSourceRecord =>
      .push .outputReverse (fun _ => .clauseMarker)
        (.goto fun _ => .copyCounter .sourceVertexClause)
  | .copyCounter stage =>
      .pop stage.stack
        (fun state symbol =>
          .unit (cursorTag state) (symbol.map fun _ => ()))
        (.branch unitIsNone
          (.load clear (.goto fun _ => .restoreCounter stage))
          (.push .scratch (fun _ => ())
            (.push .outputReverse (fun _ => .atomUnit)
              (.load clear (.goto fun _ => .copyCounter stage)))))
  | .restoreCounter stage =>
      .pop .scratch (fun state symbol => .unit (cursorTag state) symbol)
        (.branch unitIsNone
          (.load clear (afterCounter stage))
          (.push stage.stack (fun _ => stage.unit)
            (.load clear (.goto fun _ => .restoreCounter stage))))
  | .scanTarget =>
      .pop .targets (fun state symbol => .unary (cursorTag state) symbol)
        (.branch unaryIsNone
          (.load clear
            (.goto fun state => .finishSourceTarget (cursorTag state)))
          (.branch unaryIsUnit
            (.push .outputReverse (fun _ => .atomUnit)
              (.load clear (.goto fun _ => .scanTarget)))
            (.load clear
              (.goto fun state => .finishSourceTarget (cursorTag state)))))
  | .finishSourceTarget tag =>
      .push .outputReverse (fun _ => .atomEnd)
        (pushTokens (sourceSuffix tag)
          (.load clear (.goto fun _ => .beginTargetRecord)))
  | .beginTargetRecord =>
      .push .outputReverse (fun _ => .clauseMarker)
        (.goto fun _ => .copyCounter .targetVertexClause)
  | .finishTargetRecord tag =>
      .push .outputReverse (fun _ => .atomEnd)
        (pushTokens (targetSuffix tag)
          (.load clear (.goto fun _ => .incrementLink)))
  | .incrementLink =>
      .push .linkIndex (fun _ => ())
        (.load clear (.goto fun _ => .scanLinks))
  | .cleanup stage =>
      .pop stage.stack (stage.read)
        (.branch cleanupIsNone (afterCleanup stage)
          (.load clear (.goto fun _ => .cleanup stage)))
  | .reverseOutput =>
      .pop .outputReverse
        (fun state symbol => .output (cursorTag state) symbol)
        (.branch outputIsNone
          (.load clear (.goto fun _ => .cleanup .input))
          (.goto fun _ => .pushOutput))
  | .pushOutput =>
      .push .output outputFromState
        (.load clear (.goto fun _ => .reverseOutput))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanHeader
  σ := State
  initialState := .cursor initialTag
  m := program

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

end

end LeanTrominoes
