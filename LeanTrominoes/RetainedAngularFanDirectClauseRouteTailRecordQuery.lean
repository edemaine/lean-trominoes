/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordData
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedTailSemantics

/-! # Finite Figure 9 record queries for direct copied clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicCNFStripReduction

/-- All finite data needed to serialize one literal of a direct-atlas copied
clause: its logical profile and its complete normalized route lookup. -/
structure RetainedDirectRouteTailRecordLiteralQuery where
  profile : LiteralProfile
  tail : RetainedDirectSourceNormalizedTailQuery
  deriving DecidableEq, Fintype

instance : Inhabited RetainedDirectRouteTailRecordLiteralQuery :=
  ⟨⟨default, default⟩⟩

/-- Embed a genuine dependent atlas index and occurrence slot. -/
def retainedDirectRouteTailRecordLiteralQueryOfIndex
    (profile : LiteralProfile)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    RetainedDirectRouteTailRecordLiteralQuery :=
  ⟨profile,
    retainedDirectSourceNormalizedTailQueryOfIndex kind index slot⟩

/-- The clause-side direction selected by one literal record query. -/
def RetainedDirectRouteTailRecordLiteralQuery.firstDirection
    (query : RetainedDirectRouteTailRecordLiteralQuery) : AxisDirection :=
  retainedDirectSourceNormalizedDirectionOfQuery
    ⟨query.tail.kind, query.tail.literalIndex⟩

/-- The dynamic Figure 9 tail selected by one literal record query. -/
def RetainedDirectRouteTailRecordLiteralQuery.tailDirections
    (query : RetainedDirectRouteTailRecordLiteralQuery) :
    List AxisDirection :=
  retainedDirectSourceNormalizedTailOfQuery query.tail

/-- Finite sorting key shared with the semantic clockwise tail ordering. -/
def RetainedDirectRouteTailRecordLiteralQuery.key
    (query : RetainedDirectRouteTailRecordLiteralQuery) :
    LiteralProfile × AxisDirection :=
  (query.profile, query.firstDirection)

/-- Stable clockwise comparison for finite direct literal records. -/
def retainedDirectRouteTailRecordLiteralLE
    (first second : RetainedDirectRouteTailRecordLiteralQuery) : Prop :=
  FormulaShapeDirectionOrdering.directionLE first.key second.key

instance : DecidableRel retainedDirectRouteTailRecordLiteralLE := by
  intro first second
  unfold retainedDirectRouteTailRecordLiteralLE
  infer_instance

@[simp] theorem retainedDirectRouteTailRecordLiteralQueryOfIndex_firstDirection
    (profile : LiteralProfile)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    (retainedDirectRouteTailRecordLiteralQueryOfIndex
      profile kind index slot).firstDirection =
      retainedDirectSourceNormalizedFirstDirection kind index slot := by
  simpa [retainedDirectRouteTailRecordLiteralQueryOfIndex,
    RetainedDirectRouteTailRecordLiteralQuery.firstDirection,
    retainedDirectSourceNormalizedTailQueryOfIndex,
    retainedDirectSourceNormalizedDirectionQueryOfIndex] using
    retainedDirectSourceNormalizedDirectionOfQuery_index kind index slot

@[simp] theorem retainedDirectRouteTailRecordLiteralQueryOfIndex_tailDirections
    (profile : LiteralProfile)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    (retainedDirectRouteTailRecordLiteralQueryOfIndex
      profile kind index slot).tailDirections =
      retainedDirectSourceNormalizedTailOfQuery
        (retainedDirectSourceNormalizedTailQueryOfIndex kind index slot) := by
  rfl

/-- Fixed-width finite query for one nonempty direct copied clause. -/
inductive RetainedDirectClauseRouteTailRecordQuery
  | unary (first : RetainedDirectRouteTailRecordLiteralQuery)
  | binary
      (first second : RetainedDirectRouteTailRecordLiteralQuery)
  | ternary
      (first second third : RetainedDirectRouteTailRecordLiteralQuery)
  deriving DecidableEq, Fintype

instance : Inhabited RetainedDirectClauseRouteTailRecordQuery :=
  ⟨.unary default⟩

/-- Literal queries in the original clause presentation order. -/
def RetainedDirectClauseRouteTailRecordQuery.literalQueries :
    RetainedDirectClauseRouteTailRecordQuery →
      List RetainedDirectRouteTailRecordLiteralQuery
  | .unary first => [first]
  | .binary first second => [first, second]
  | .ternary first second third => [first, second, third]

/-- Evaluate the finite literal fields to the exact directed clause profile. -/
def RetainedDirectClauseRouteTailRecordQuery.directedProfile
    (query : RetainedDirectClauseRouteTailRecordQuery) :
    FormulaShapeDirectionOrdering.DirectedClauseProfile :=
  FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
    (query.literalQueries.map
      RetainedDirectRouteTailRecordLiteralQuery.key)

/-- Evaluate the finite literal fields to the stably clockwise-sorted dynamic
tail table, while leaving `directedProfile` in presentation order. -/
def RetainedDirectClauseRouteTailRecordQuery.tailTable
    (query : RetainedDirectClauseRouteTailRecordQuery) :
    List (List AxisDirection) :=
  (query.literalQueries.insertionSort
    retainedDirectRouteTailRecordLiteralLE).map
      RetainedDirectRouteTailRecordLiteralQuery.tailDirections

/-- Exact flat Figure 9 input record selected by one finite direct query. -/
def retainedDirectClauseRouteTailRecordTokens
    (query : RetainedDirectClauseRouteTailRecordQuery) :
    List HorizontalRoutedRouteTailRecord.Token :=
  HorizontalRoutedRouteTailRecord.clauseRecord
    query.directedProfile query.tailTable

/-- Concatenated Figure 9 record stream selected by direct clause queries. -/
def retainedDirectClauseRouteTailRecordStream
    (queries : List RetainedDirectClauseRouteTailRecordQuery) :
    List HorizontalRoutedRouteTailRecord.Token :=
  queries.flatMap retainedDirectClauseRouteTailRecordTokens

end PeriodicEightOccurrenceSplit
end LeanTrominoes
