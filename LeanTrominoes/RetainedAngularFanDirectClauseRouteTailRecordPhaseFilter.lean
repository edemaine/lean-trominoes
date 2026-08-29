/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachment

/-! # Phase filters for direct clause route-tail inputs -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Recover the direct-atlas family stored by the first literal query.
Canonical direct clauses use one common family on every literal; malformed
or precomputed queries deliberately return `none`. -/
def RetainedFinalCopiedClauseQuery.directKind? :
    RetainedFinalCopiedClauseQuery → Option RetainedDirectClauseKind
  | .unary _ (.direct query) => some query.kind
  | .binary _ (.direct query) _ _ => some query.kind
  | .ternary _ (.direct query) _ _ _ _ => some query.kind
  | _ => none

/-- Whether a query belongs to the fixed crossover prefix. -/
def RetainedFinalCopiedClauseQuery.isDirectCrossover
    (query : RetainedFinalCopiedClauseQuery) : Bool :=
  match query.directKind? with
  | some (.crossover _) => true
  | _ => false

/-- Whether a query belongs to either routed direct suffix family. -/
def RetainedFinalCopiedClauseQuery.isDirectRouted
    (query : RetainedFinalCopiedClauseQuery) : Bool :=
  match query.directKind? with
  | some (.duplicator _ _) => true
  | some .routedClause => true
  | _ => false

/-- Retain one slot input exactly when its query belongs to the crossover
direct-atlas family. -/
def retainedDirectCrossoverRouteTailRecordSlotInputBlock
    (input : RetainedDirectClauseRouteTailRecordSlotInput) :
    List RetainedDirectClauseRouteTailRecordSlotInput :=
  if input.1.isDirectCrossover then [input] else []

/-- Retain one slot input exactly when its query belongs to a routed direct
atlas family. -/
def retainedDirectRoutedRouteTailRecordSlotInputBlock
    (input : RetainedDirectClauseRouteTailRecordSlotInput) :
    List RetainedDirectClauseRouteTailRecordSlotInput :=
  if input.1.isDirectRouted then [input] else []

/-- Crossover phase of an arbitrary slot-input stream. -/
def retainedDirectCrossoverRouteTailRecordSlotInputs
    (inputs : List RetainedDirectClauseRouteTailRecordSlotInput) :
    List RetainedDirectClauseRouteTailRecordSlotInput :=
  inputs.flatMap retainedDirectCrossoverRouteTailRecordSlotInputBlock

/-- Combined routed-clause/routed-variable phase of an arbitrary slot-input
stream. -/
def retainedDirectRoutedRouteTailRecordSlotInputs
    (inputs : List RetainedDirectClauseRouteTailRecordSlotInput) :
    List RetainedDirectClauseRouteTailRecordSlotInput :=
  inputs.flatMap retainedDirectRoutedRouteTailRecordSlotInputBlock

@[simp] theorem retainedDirectCrossoverRouteTailRecordSlotInputs_append
    (first second : List RetainedDirectClauseRouteTailRecordSlotInput) :
    retainedDirectCrossoverRouteTailRecordSlotInputs (first ++ second) =
      retainedDirectCrossoverRouteTailRecordSlotInputs first ++
        retainedDirectCrossoverRouteTailRecordSlotInputs second := by
  unfold retainedDirectCrossoverRouteTailRecordSlotInputs
  exact List.flatMap_append

@[simp] theorem retainedDirectRoutedRouteTailRecordSlotInputs_append
    (first second : List RetainedDirectClauseRouteTailRecordSlotInput) :
    retainedDirectRoutedRouteTailRecordSlotInputs (first ++ second) =
      retainedDirectRoutedRouteTailRecordSlotInputs first ++
        retainedDirectRoutedRouteTailRecordSlotInputs second := by
  unfold retainedDirectRoutedRouteTailRecordSlotInputs
  exact List.flatMap_append

end PeriodicEightOccurrenceSplit
end LeanTrominoes
