/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterData

/-! # Finite source-occurrence route emitter machine

The machine first separates the finite occurrence stream from its aligned
unary target-index stream, counting clause and literal headers along the way.
It then scans occurrences and emits every counted eleven-field route record.
All unbounded numeric state lives on unary work tapes.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

abbrev InputSymbol := SourceOccurrenceRouteEmitter.InputSymbol
abbrev OccurrenceToken := SourceOccurrenceRouteTokens.Token
abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol
abbrev OutputToken := UnaryProgramTokens.Token

local instance : Inhabited InputSymbol := ⟨.separator⟩

/-- Finite control retained while the unbounded counters stay on tapes. -/
structure Cursor where
  seenClause : Bool
  literalIndex : Fin 3
  anchorNext : Option Bool
  currentNext : Bool
  deriving DecidableEq, Fintype

def initialCursor : Cursor where
  seenClause := false
  literalIndex := 0
  anchorNext := none
  currentNext := false

inductive Stack
  | input
  | occurrenceReverse
  | occurrences
  | targetReverse
  | targets
  | clauseCount
  | literalCount
  | clauseIndex
  | edgeIndex
  | scratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

/-- Each stage copies one unary counter without consuming it. -/
inductive CounterStage
  | vertexClauses
  | vertexLiteralsFirst
  | vertexLiteralsSecond
  | edgeLiteralsFirst
  | edgeLiteralsSecond
  | edgeLiteralsThird
  | edgeIndex
  | sourceLiterals
  | sourceClauses
  deriving DecidableEq, Fintype

def CounterStage.stack : CounterStage → Stack
  | .vertexClauses => .clauseCount
  | .vertexLiteralsFirst | .vertexLiteralsSecond |
      .edgeLiteralsFirst | .edgeLiteralsSecond | .edgeLiteralsThird |
      .sourceLiterals => .literalCount
  | .edgeIndex => .edgeIndex
  | .sourceClauses => .clauseIndex

inductive Label
  | scanLeft
  | pushOccurrence
  | scanRight
  | pushTargetReverse
  | restoreOccurrences
  | pushOccurrenceForward
  | restoreTargets
  | pushTargetForward
  | scanOccurrences
  | beginRecord
  | copyCounter (stage : CounterStage)
  | restoreCounter (stage : CounterStage)
  | scanTarget
  | finishRecord (literalIndex : Fin 3) (currentNext anchorNext : Bool)
  | reverseOutput
  | pushOutput
  deriving Fintype

/-- Transitions temporarily hold one typed tape symbol together with the
finite route cursor. -/
inductive State
  | cursor (cursor : Cursor)
  | input (cursor : Cursor) (symbol : Option InputSymbol)
  | occurrence (cursor : Cursor) (symbol : Option OccurrenceToken)
  | unary (cursor : Cursor) (symbol : Option UnarySymbol)
  | unit (cursor : Cursor) (symbol : Option Unit)
  | output (cursor : Cursor) (symbol : Option OutputToken)
  deriving Fintype

abbrev Alphabet : Stack → Type
  | .input => InputSymbol
  | .occurrenceReverse | .occurrences => OccurrenceToken
  | .targetReverse | .targets => UnarySymbol
  | .clauseCount | .literalCount | .clauseIndex | .edgeIndex | .scratch =>
      Unit
  | .outputReverse | .output => OutputToken

def CounterStage.unit (stage : CounterStage) : Alphabet stage.stack := by
  cases stage <;> exact ()

def cursorFromState : State → Cursor
  | .cursor cursor | .input cursor _ | .occurrence cursor _ |
      .unary cursor _ | .unit cursor _ | .output cursor _ => cursor

def clear (state : State) : State := .cursor (cursorFromState state)

def inputFromState : State → InputSymbol
  | .input _ (some symbol) => symbol
  | _ => default

def occurrenceFromState : State → OccurrenceToken
  | .occurrence _ (some token) => token
  | .input _ (some (.left token)) => token
  | _ => default

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

def inputIsLeft : State → Bool
  | .input _ (some (.left _)) => true
  | _ => false

def inputIsSeparator : State → Bool
  | .input _ (some .separator) => true
  | _ => false

def inputIsRight : State → Bool
  | .input _ (some (.right _)) => true
  | _ => false

def inputLeftIsClause : State → Bool
  | .input _ (some (.left (.clause _))) => true
  | _ => false

def inputLeftIsLiteral : State → Bool
  | .input _ (some (.left (.literal _))) => true
  | _ => false

def occurrenceIsNone : State → Bool
  | .occurrence _ none => true
  | _ => false

def occurrenceIsClause : State → Bool
  | .occurrence _ (some (.clause _)) => true
  | _ => false

def occurrenceIsLiteral : State → Bool
  | .occurrence _ (some (.literal _)) => true
  | _ => false

def occurrenceIsOffset : State → Bool
  | .occurrence _ (some (.offsetNext _)) => true
  | _ => false

def cursorSeenClause (state : State) : Bool :=
  (cursorFromState state).seenClause

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

def startClause : State → State
  | state =>
      let cursor := cursorFromState state
      .cursor { cursor with seenClause := true, anchorNext := none }

def setLiteral : State → State
  | .occurrence cursor (some (.literal index)) =>
      .cursor { cursor with literalIndex := index }
  | state => clear state

def setOffset : State → State
  | .occurrence cursor (some (.offsetNext value)) =>
      .cursor
        { cursor with
          anchorNext := some (cursor.anchorNext.getD value)
          currentNext := value }
  | state => clear state

def Cursor.anchorValue (cursor : Cursor) : Bool :=
  cursor.anchorNext.getD cursor.currentNext

def positiveOffsetTokens (currentNext anchorNext : Bool) : List OutputToken :=
  match currentNext, anchorNext with
  | true, false => [.atomUnit]
  | _, _ => []

def negativeOffsetTokens (currentNext anchorNext : Bool) : List OutputToken :=
  match currentNext, anchorNext with
  | false, true => [.atomUnit]
  | _, _ => []

/-- Fixed suffix after the streamed target-index field: source and target
ports followed by the four signed offset fields. -/
def fixedSuffix (literalIndex : Fin 3)
    (currentNext anchorNext : Bool) : List OutputToken :=
  List.replicate literalIndex.val .atomUnit ++
    [.atomEnd, .atomEnd] ++
    positiveOffsetTokens currentNext anchorNext ++ [.atomEnd] ++
    negativeOffsetTokens currentNext anchorNext ++
    [.atomEnd, .atomEnd, .atomEnd]

def pushTokens (tokens : List OutputToken)
    (next : TM2.Stmt Alphabet Label State) :
    TM2.Stmt Alphabet Label State :=
  tokens.foldr
    (fun token continuation =>
      .push .outputReverse (fun _ => token) continuation)
    next

def afterCounter : CounterStage → TM2.Stmt Alphabet Label State
  | .vertexClauses => .goto fun _ => .copyCounter .vertexLiteralsFirst
  | .vertexLiteralsFirst =>
      .goto fun _ => .copyCounter .vertexLiteralsSecond
  | .vertexLiteralsSecond =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .edgeLiteralsFirst)
  | .edgeLiteralsFirst =>
      .goto fun _ => .copyCounter .edgeLiteralsSecond
  | .edgeLiteralsSecond =>
      .goto fun _ => .copyCounter .edgeLiteralsThird
  | .edgeLiteralsThird =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .edgeIndex)
  | .edgeIndex =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .copyCounter .sourceLiterals)
  | .sourceLiterals => .goto fun _ => .copyCounter .sourceClauses
  | .sourceClauses =>
      .push .outputReverse (fun _ => .atomEnd)
        (.goto fun _ => .scanTarget)

def program : Label → TM2.Stmt Alphabet Label State
  | .scanLeft =>
      .pop .input (fun state symbol => .input (cursorFromState state) symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restoreOccurrences))
          (.branch inputIsLeft
            (.goto fun _ => .pushOccurrence)
            (.branch inputIsSeparator
              (.load clear (.goto fun _ => .scanRight))
              (.load clear (.goto fun _ => .scanLeft)))))
  | .pushOccurrence =>
      .push .occurrenceReverse occurrenceFromState
        (.branch inputLeftIsClause
          (.push .clauseCount (fun _ => ())
            (.load clear (.goto fun _ => .scanLeft)))
          (.branch inputLeftIsLiteral
            (.push .literalCount (fun _ => ())
              (.load clear (.goto fun _ => .scanLeft)))
            (.load clear (.goto fun _ => .scanLeft))))
  | .scanRight =>
      .pop .input (fun state symbol => .input (cursorFromState state) symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restoreOccurrences))
          (.branch inputIsRight
            (.goto fun _ => .pushTargetReverse)
            (.load clear (.goto fun _ => .scanRight))))
  | .pushTargetReverse =>
      .push .targetReverse unaryFromState
        (.load clear (.goto fun _ => .scanRight))
  | .restoreOccurrences =>
      .pop .occurrenceReverse
        (fun state symbol => .occurrence (cursorFromState state) symbol)
        (.branch occurrenceIsNone
          (.load clear (.goto fun _ => .restoreTargets))
          (.goto fun _ => .pushOccurrenceForward))
  | .pushOccurrenceForward =>
      .push .occurrences occurrenceFromState
        (.load clear (.goto fun _ => .restoreOccurrences))
  | .restoreTargets =>
      .pop .targetReverse
        (fun state symbol => .unary (cursorFromState state) symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .scanOccurrences))
          (.goto fun _ => .pushTargetForward))
  | .pushTargetForward =>
      .push .targets unaryFromState
        (.load clear (.goto fun _ => .restoreTargets))
  | .scanOccurrences =>
      .pop .occurrences
        (fun state symbol => .occurrence (cursorFromState state) symbol)
        (.branch occurrenceIsNone
          (.load clear (.goto fun _ => .reverseOutput))
          (.branch occurrenceIsClause
            (.branch cursorSeenClause
              (.push .clauseIndex (fun _ => ())
                (.load startClause (.goto fun _ => .scanOccurrences)))
              (.load startClause (.goto fun _ => .scanOccurrences)))
            (.branch occurrenceIsLiteral
              (.load setLiteral (.goto fun _ => .scanOccurrences))
              (.branch occurrenceIsOffset
                (.load setOffset (.goto fun _ => .beginRecord))
                (.load clear (.goto fun _ => .scanOccurrences))))))
  | .beginRecord =>
      .push .outputReverse (fun _ => .clauseMarker)
        (.goto fun _ => .copyCounter .vertexClauses)
  | .copyCounter stage =>
      .pop stage.stack
        (fun state symbol =>
          .unit (cursorFromState state) (symbol.map fun _ => ()))
        (.branch unitIsNone
          (.load clear (.goto fun _ => .restoreCounter stage))
          (.push .scratch (fun _ => ())
            (.push .outputReverse (fun _ => .atomUnit)
              (.load clear (.goto fun _ => .copyCounter stage)))))
  | .restoreCounter stage =>
      .pop .scratch
        (fun state symbol => .unit (cursorFromState state) symbol)
        (.branch unitIsNone
          (.load clear (afterCounter stage))
          (.push stage.stack (fun _ => stage.unit)
            (.load clear (.goto fun _ => .restoreCounter stage))))
  | .scanTarget =>
      .pop .targets
        (fun state symbol => .unary (cursorFromState state) symbol)
        (.branch unaryIsNone
          (.push .outputReverse (fun _ => .atomEnd)
            (.goto fun state =>
              let cursor := cursorFromState state
              .finishRecord cursor.literalIndex cursor.currentNext
                cursor.anchorValue))
          (.branch unaryIsUnit
            (.push .outputReverse (fun _ => .atomUnit)
              (.load clear (.goto fun _ => .scanTarget)))
            (.push .outputReverse (fun _ => .atomEnd)
              (.goto fun state =>
                let cursor := cursorFromState state
                .finishRecord cursor.literalIndex cursor.currentNext
                  cursor.anchorValue))))
  | .finishRecord literalIndex currentNext anchorNext =>
      pushTokens (fixedSuffix literalIndex currentNext anchorNext)
        (.push .edgeIndex (fun _ => ())
          (.load clear (.goto fun _ => .scanOccurrences)))
  | .reverseOutput =>
      .pop .outputReverse
        (fun state symbol => .output (cursorFromState state) symbol)
        (.branch outputIsNone
          (.load clear .halt)
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
  main := .scanLeft
  σ := State
  initialState := .cursor initialCursor
  m := program

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end
end LeanTrominoes
