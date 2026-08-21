/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkData
import LeanTrominoes.PeriodicCNFPlanarIncidences

/-! # Fixed incidence blocks for occurrence-cycle links -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The negative-source and positive-target incidence records of one globally
indexed implication-cycle link. -/
def cycleLinkIncidenceBlock {Variable : Type*}
    (taggedLink :
      (ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable) × Nat) :
    List (CNFIncidence (ThreeOccurrenceVariable Variable)) :=
  let clause := implicationClause taggedLink.1.1 taggedLink.1.2
  [⟨taggedLink.2, clause, 0,
      ⟨taggedLink.1.1, (0, 0), false⟩⟩,
    ⟨taggedLink.2, clause, 1,
      ⟨taggedLink.1.2, (0, 0), true⟩⟩]

/-- All fixed two-incidence blocks, with clause indices beginning after the
copied source clauses. -/
def cycleLinkIncidences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (CNFIncidence (ThreeOccurrenceVariable Variable)) :=
  (allCycleLinks source).zipIdx source.clauses.length |>.flatMap
    cycleLinkIncidenceBlock

@[simp] theorem cycleLinkIncidenceBlock_length
    {Variable : Type*}
    (taggedLink :
      (ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable) × Nat) :
    (cycleLinkIncidenceBlock taggedLink).length = 2 := by
  rfl

end PeriodicThreeSATThree
end LeanTrominoes
