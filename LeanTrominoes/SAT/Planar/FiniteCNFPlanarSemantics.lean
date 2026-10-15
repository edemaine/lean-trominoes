/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteCNFZeroOffsets
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarPeriodicSoundness

/-! # Ordinary finite SAT semantics of the complete routed block

This statement concerns the finite Boolean formula before periodicization.
It does not claim that the complete neighboring block is a planar drawing;
the retained geometric assembly is a separate construction.
-/
namespace LeanTrominoes.FiniteCNF
open PeriodicOrthocrossing PlanarThreeSAT

theorem clauseAnchor_periodize_clause {V : Type*} (clause : Clause V) :
    PeriodicCNF.clauseAnchor (clause.map fun literal =>
      (⟨literal.1,(0,0),literal.2⟩ : PeriodicLiteral V))=(0,0) := by
  cases clause <;> rfl

theorem routedBlock_satisfiable_iff {V : Type*} [DecidableEq V] (formula : Formula V)
    (occurrences : (periodize formula).OccurrencesAtMost 3) :
    (∃ assignment, FormulaHolds assignment (drawingPlanarSATFormula (periodize formula))) ↔
      Satisfiable formula := by
  constructor
  · rintro ⟨assignment,holds⟩
    refine ⟨fun atom => assignment (.inl (.atom (atom,(0,0)))),?_⟩
    intro clause member
    let embedded : PeriodicClause V := clause.map fun literal => ⟨literal.1,(0,0),literal.2⟩
    have embeddedMem : embedded∈(periodize formula).clauses := List.mem_map.mpr ⟨clause,member,rfl⟩
    have taggedMem : embedded∈(periodize formula).clauses.zipIdx.map Prod.fst := by
      simpa only [List.zipIdx_map_fst] using embeddedMem
    obtain ⟨tagged,member,eq⟩ := List.mem_map.mp taggedMem
    have original := drawingPlanarSATFormula_source_clause_holds (periodize formula)
      occurrences assignment holds tagged member (0,0) ⟨by simp,by simp⟩
    rw [eq] at original
    obtain ⟨literal,hl,truth⟩ := original
    obtain ⟨originalLiteral,originalMember,literalEq⟩ := List.mem_map.mp hl
    subst literal
    refine ⟨originalLiteral,originalMember,?_⟩
    simpa [embedded,clauseAnchor_periodize_clause,PeriodicLiteral.Holds,
      finitePlanarSATAtomAssignment,Cell.sub,Cell.add] using truth
  · rintro ⟨assignment,holds⟩
    exact exists_drawingPlanarSATFormula_holds_of_satisfies (periodize formula)
      (fun atom _ => assignment atom) ((satisfies_periodize formula _).mpr (fun _ => holds))

end LeanTrominoes.FiniteCNF
