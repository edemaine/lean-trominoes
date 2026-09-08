/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripTypedElementCodes
import LeanTrominoes.PeriodicThreeDMGraph

/-! # Structural codes of actual typed incidence references -/

namespace LeanTrominoes.PeriodicCNFStripReduction.TypedElementCode

open Gadget PlanarThreeDM PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

variable {Variable : Type*}

/-- Read the structural name of one colored typed reference. -/
def reference (key : Variable × OccurrenceSlot → Nat)
    (references : TripleReferences Variable) : WireColor → Nat
  | .red => red key references.red.atom
  | .green => green key references.green.atom
  | .blue => blue key references.blue.atom

/-- The finite clause-reference tag is its structural name at clause zero. -/
def clauseReferenceTag (set : X3CClauseSet) (color : WireColor) : Nat :=
  reference (Variable := Unit) (fun _ => 0) (clauseTripleReferences 0 set) color

/-- The actual clause index contributes exactly its stride-scaled base; the
remaining reference tag is independent of the source and occurrence keys. -/
theorem reference_clause (key : Variable × OccurrenceSlot → Nat)
    (index : Nat) (set : X3CClauseSet) (color : WireColor) :
    reference key (clauseTripleReferences index set) color =
      index * 32 + clauseReferenceTag set color := by
  cases set <;> cases color <;> rfl

/-- All 27 clause incidences retain their triple-major red/green/blue order. -/
def clauseIncidenceBlock (index : Nat) : List Nat :=
  allClauseSets.flatMap fun set => incidenceColors.map fun color =>
    index * 32 + clauseReferenceTag set color

/-- Coding the typed clause-triple suffix produces one complete fixed block
at every actual clause position. -/
theorem clauseTriples_codes_eq [DecidableEq Variable] (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) :
    (clauseTriples source).flatMap (fun triple => incidenceColors.map fun color =>
      reference key (tripleReferences source triple) color) =
      (List.range source.clauses.length).flatMap clauseIncidenceBlock := by
  simp only [clauseTriples, List.flatMap_assoc, List.flatMap_map, tripleReferences]
  apply List.flatMap_congr
  intro index _
  unfold clauseIncidenceBlock
  apply List.flatMap_congr
  intro set _
  apply List.map_congr_left
  intro color _
  exact reference_clause key index set color

end LeanTrominoes.PeriodicCNFStripReduction.TypedElementCode
