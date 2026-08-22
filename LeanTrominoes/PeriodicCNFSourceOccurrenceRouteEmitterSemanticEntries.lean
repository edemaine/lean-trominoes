/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataAppend
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordSemantics

/-! # Semantic entries consumed by the source-occurrence route emitter -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

/-- One source incidence paired with its global occurrence-edge index. -/
abbrev SemanticEntry := CNFIncidence Nat × Nat

/-- Occurrence entries for a suffix of one clause, carrying both the next
literal index and the next global occurrence-edge index. -/
def clauseEntriesFrom (clause : PeriodicClause Nat)
    (clauseIndex literalIndex edgeIndex : Nat) :
    List (PeriodicLiteral Nat) → List SemanticEntry
  | [] => []
  | literal :: literals =>
      (⟨clauseIndex, clause, literalIndex, literal⟩, edgeIndex) ::
        clauseEntriesFrom clause clauseIndex (literalIndex + 1)
          (edgeIndex + 1) literals

/-- Occurrence entries for a suffix of the clause presentation, carrying
the next clause and global occurrence-edge indices. -/
def formulaEntriesFrom :
    List (PeriodicClause Nat) → Nat → Nat → List SemanticEntry
  | [], _, _ => []
  | clause :: clauses, clauseIndex, edgeIndex =>
      clauseEntriesFrom clause clauseIndex 0 edgeIndex clause ++
        formulaEntriesFrom clauses (clauseIndex + 1)
          (edgeIndex + clause.length)

/-- Literal-index register after scanning a suffix of literal blocks. -/
def literalIndexAfter (oldLiteralIndex : Fin 3) (literalIndex : Nat) :
    List (PeriodicLiteral Nat) → Fin 3
  | [] => oldLiteralIndex
  | _ :: literals =>
      literalIndexAfter (SourceOccurrenceTokens.literalIndex literalIndex)
        (literalIndex + 1) literals

/-- Anchor bit retained after a clause header and all of its literals. -/
def clauseAnchorState : List (PeriodicLiteral Nat) → Option Bool
  | [] => none
  | literal :: _ => some (SourceForwardOffset.isNext literal)

/-- Target indices consumed while emitting a semantic entry list. -/
def entryTargets (source : PeriodicCNF Nat)
    (entries : List SemanticEntry) : List Nat :=
  entries.map fun entry =>
    (PeriodicThreeSATThree.occurrenceRouteDescriptor
      source entry.1 entry.2).targetVertexIndex

/-- Counted route-token blocks expected from a semantic entry list. -/
def entryTokens (source : PeriodicCNF Nat)
    (entries : List SemanticEntry) :
    List UnaryProgramTokens.Token :=
  entries.flatMap fun entry =>
    CountedUnaryFieldTokens.countedFieldBlock
      (PeriodicThreeSATThree.occurrenceRouteDescriptor
        source entry.1 entry.2).unaryFields

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
