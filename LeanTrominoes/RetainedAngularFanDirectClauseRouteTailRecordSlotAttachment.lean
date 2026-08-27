/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordQuery
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery

/-! # Attaching occurrence slots to finite direct clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

/-- Fixed-width occurrence slots belonging to one nonempty direct clause. -/
inductive RetainedDirectClauseOccurrenceSlots
  | unary (first : RetainedTerminalSlot)
  | binary (first second : RetainedTerminalSlot)
  | ternary
      (first second third : RetainedTerminalSlot)
  deriving DecidableEq, Fintype

instance : Inhabited RetainedDirectClauseOccurrenceSlots :=
  ⟨.unary default⟩

/-- Total width-three slot packing. Genuine source clauses use only the
nonempty branches of width at most three. -/
def RetainedDirectClauseOccurrenceSlots.ofList :
    List RetainedTerminalSlot → RetainedDirectClauseOccurrenceSlots
  | [] => default
  | [first] => .unary first
  | [first, second] => .binary first second
  | first :: second :: third :: _ => .ternary first second third

/-- One already-compiled finite direction query paired with its bounded
presentation-ordered occurrence slots. -/
abbrev RetainedDirectClauseRouteTailRecordSlotInput :=
  RetainedFinalCopiedClauseQuery × RetainedDirectClauseOccurrenceSlots

/-- Attach one slot to one finite direct-atlas literal query. -/
def retainedDirectRouteTailRecordLiteralQueryOfDirectionQuery
    (profile : LiteralProfile)
    (query : RetainedDirectSourceNormalizedDirectionQuery)
    (slot : RetainedTerminalSlot) :
    RetainedDirectRouteTailRecordLiteralQuery :=
  ⟨profile, ⟨query.kind, query.literalIndex, slot⟩⟩

/-- Attach matching slot tuples to direct unary, binary, or ternary clause
queries. Fallback, precomputed, and arity-mismatched inputs are rejected. -/
def retainedDirectClauseRouteTailRecordQueryOfSlotInput :
    RetainedDirectClauseRouteTailRecordSlotInput →
      Option RetainedDirectClauseRouteTailRecordQuery
  | (.unary first (.direct firstQuery), .unary firstSlot) =>
      some (.unary
        (retainedDirectRouteTailRecordLiteralQueryOfDirectionQuery
          first firstQuery firstSlot))
  | (.binary first (.direct firstQuery)
        second (.direct secondQuery),
      .binary firstSlot secondSlot) =>
      some (.binary
        (retainedDirectRouteTailRecordLiteralQueryOfDirectionQuery
          first firstQuery firstSlot)
        (retainedDirectRouteTailRecordLiteralQueryOfDirectionQuery
          second secondQuery secondSlot))
  | (.ternary first (.direct firstQuery)
        second (.direct secondQuery)
        third (.direct thirdQuery),
      .ternary firstSlot secondSlot thirdSlot) =>
      some (.ternary
        (retainedDirectRouteTailRecordLiteralQueryOfDirectionQuery
          first firstQuery firstSlot)
        (retainedDirectRouteTailRecordLiteralQueryOfDirectionQuery
          second secondQuery secondSlot)
        (retainedDirectRouteTailRecordLiteralQueryOfDirectionQuery
          third thirdQuery thirdSlot))
  | _ => none

/-- Elementwise successful attachment over a finite input stream. -/
def retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
    (inputs : List RetainedDirectClauseRouteTailRecordSlotInput) :
    List RetainedDirectClauseRouteTailRecordQuery :=
  inputs.flatMap fun input =>
    (retainedDirectClauseRouteTailRecordQueryOfSlotInput input).toList

/-- Erase one full-tail literal back to its previously compiled finite
direction query item. -/
def RetainedDirectRouteTailRecordLiteralQuery.directionQueryItem
    (query : RetainedDirectRouteTailRecordLiteralQuery) :
    LiteralProfile × RetainedFinalCopiedSourceDirectionQuery :=
  (query.profile,
    .direct ⟨query.tail.kind, query.tail.literalIndex⟩)

/-- Erase full-tail slots back to the previously compiled direct-direction
query alphabet. -/
def RetainedDirectClauseRouteTailRecordQuery.directionQuery
    (query : RetainedDirectClauseRouteTailRecordQuery) :
    RetainedFinalCopiedClauseQuery :=
  RetainedFinalCopiedClauseQuery.ofList
    (query.literalQueries.map
      RetainedDirectRouteTailRecordLiteralQuery.directionQueryItem)

/-- Extract the bounded slot tuple from a full direct record query. -/
def RetainedDirectClauseRouteTailRecordQuery.occurrenceSlots
    (query : RetainedDirectClauseRouteTailRecordQuery) :
    RetainedDirectClauseOccurrenceSlots :=
  RetainedDirectClauseOccurrenceSlots.ofList
    (query.literalQueries.map fun literalQuery =>
      literalQuery.tail.slot)

/-- Slot attachment is lossless on every well-formed full direct query. -/
@[simp] theorem retainedDirectClauseRouteTailRecordQueryOfSlotInput_roundtrip
    (query : RetainedDirectClauseRouteTailRecordQuery) :
    retainedDirectClauseRouteTailRecordQueryOfSlotInput
        (query.directionQuery, query.occurrenceSlots) =
      some query := by
  cases query <;> rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
