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

/-- Erase full-tail slots back to the previously compiled direct-direction
query alphabet. -/
def RetainedDirectClauseRouteTailRecordQuery.directionQuery :
    RetainedDirectClauseRouteTailRecordQuery → RetainedFinalCopiedClauseQuery
  | .unary first =>
      .unary first.profile (.direct
        ⟨first.tail.kind, first.tail.literalIndex⟩)
  | .binary first second =>
      .binary first.profile (.direct
          ⟨first.tail.kind, first.tail.literalIndex⟩)
        second.profile (.direct
          ⟨second.tail.kind, second.tail.literalIndex⟩)
  | .ternary first second third =>
      .ternary first.profile (.direct
          ⟨first.tail.kind, first.tail.literalIndex⟩)
        second.profile (.direct
          ⟨second.tail.kind, second.tail.literalIndex⟩)
        third.profile (.direct
          ⟨third.tail.kind, third.tail.literalIndex⟩)

/-- Extract the bounded slot tuple from a full direct record query. -/
def RetainedDirectClauseRouteTailRecordQuery.occurrenceSlots :
    RetainedDirectClauseRouteTailRecordQuery →
      RetainedDirectClauseOccurrenceSlots
  | .unary first => .unary first.tail.slot
  | .binary first second =>
      .binary first.tail.slot second.tail.slot
  | .ternary first second third =>
      .ternary first.tail.slot second.tail.slot third.tail.slot

/-- Slot attachment is lossless on every well-formed full direct query. -/
@[simp] theorem retainedDirectClauseRouteTailRecordQueryOfSlotInput_roundtrip
    (query : RetainedDirectClauseRouteTailRecordQuery) :
    retainedDirectClauseRouteTailRecordQueryOfSlotInput
        (query.directionQuery, query.occurrenceSlots) =
      some query := by
  cases query <;> rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
