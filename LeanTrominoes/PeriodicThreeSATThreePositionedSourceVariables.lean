/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned

/-!
# Positioned witnesses for source variables

The occurrence-splitting construction records only the duplicate-free list
of atoms occurring in the erased periodic formula.  Geometric arguments need
an actual positioned clause/literal incidence witnessing such membership.
This file recovers that incidence without changing its presentation indices.
-/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Every atom in the duplicate-free source-variable list of a positioned
formula is witnessed by a genuine positioned clause/literal incidence. -/
theorem exists_positioned_members_of_mem_sourceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {atom : Variable}
    (atomMember : atom ∈ sourceVariables source.erase) :
    ∃ clause : PositionedPeriodicClause Variable,
      ∃ clauseIndex : Nat,
        ∃ literal : PeriodicLiteral Variable,
          ∃ literalIndex : Nat,
            (clause, clauseIndex) ∈ source.clauses.zipIdx ∧
              (literal, literalIndex) ∈
                clause.literals.zipIdx ∧
              literal.atom = atom := by
  rw [sourceVariables, List.mem_dedup,
    List.mem_map] at atomMember
  rcases atomMember with
    ⟨tagged, taggedMember, atomEqual⟩
  rw [taggedLiterals, List.mem_flatMap] at taggedMember
  rcases taggedMember with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteralMember⟩
  rcases List.mem_map.mp taggedLiteralMember with
    ⟨taggedLiteral, taggedLiteralMember,
      taggedEqual⟩
  have erasedClauseLookup :
      source.erase.clauses[taggedClause.2]? =
        some taggedClause.1 :=
    (List.mem_zipIdx_iff_getElem?).mp taggedClauseMember
  change
    (source.clauses.map
      PositionedPeriodicClause.literals)[taggedClause.2]? =
        some taggedClause.1
    at erasedClauseLookup
  rw [List.getElem?_map] at erasedClauseLookup
  simp only [Option.map_eq_some_iff] at erasedClauseLookup
  rcases erasedClauseLookup with
    ⟨clause, clauseLookup, clauseLiteralsEqual⟩
  have clauseMember :
      (clause, taggedClause.2) ∈
        source.clauses.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr clauseLookup
  have literalMember :
      (taggedLiteral.1, taggedLiteral.2) ∈
        clause.literals.zipIdx := by
    rw [clauseLiteralsEqual]
    exact taggedLiteralMember
  refine
    ⟨clause, taggedClause.2,
      taggedLiteral.1, taggedLiteral.2,
      clauseMember, literalMember, ?_⟩
  rw [← atomEqual]
  exact congrArg (fun tagged => tagged.1.atom)
    taggedEqual

end PeriodicThreeSATThree
end LeanTrominoes
