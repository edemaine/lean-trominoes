/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlanarThreeSATFamilies
import LeanTrominoes.PlanarThreeSATWires

/-! # Common-offset properties of finite clause gadget families -/
namespace LeanTrominoes.PlanarThreeSAT

def UniformOffsets {V : Type*} (offset : V → Cell) (clauses : List (EmbeddedClause V)) : Prop :=
  ∀ clause∈clauses, ∃ common, ∀ literal∈clause.literals, offset literal.1=common

theorem uniformOffsets_append {V : Type*} (offset : V → Cell) (first second : List (EmbeddedClause V))
    (a : UniformOffsets offset first) (b : UniformOffsets offset second) :
    UniformOffsets offset (first++second) := by
  intro clause member
  exact (List.mem_append.mp member).elim (a clause) (b clause)

theorem uniformOffsets_map {V W : Type*} (offset : W → Cell) (f : V → W)
    (positionMap : Cell → Cell) (clauses : List (EmbeddedClause V))
    (uniform : UniformOffsets (offset ∘ f) clauses) :
    UniformOffsets offset (clauses.map (EmbeddedClause.map f positionMap)) := by
  intro clause member
  obtain ⟨original,originalMember,clauseEq⟩ := List.mem_map.mp member
  subst clause
  obtain ⟨common,all⟩ := uniform original originalMember
  refine ⟨common,?_⟩
  intro literal hl
  obtain ⟨oldLiteral,oldMember,literalEq⟩ := List.mem_map.mp hl
  subst literal
  exact all oldLiteral oldMember

theorem uniformOffsets_equalityFamily {V : Type*} (offset : V → Cell)
    (links : List (EqualityLink V))
    (equal : ∀ link∈links, offset link.first=offset link.second) :
    UniformOffsets offset (equalityFamily links) := by
  intro clause member
  obtain ⟨link,linkMember,clauseMember⟩ := List.mem_flatMap.mp member
  refine ⟨offset link.first,?_⟩
  simp only [equalityInstance,List.mem_cons,List.not_mem_nil,or_false] at clauseMember
  rcases clauseMember with rfl|rfl <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] <;>
    exact ⟨True.intro,(equal link linkMember).symm⟩

theorem uniformOffsets_crossoverFamily {Site V : Type*}
    (offset : Sum V (Site×CrossoverInternal) → Cell) (sites : List Site)
    (ports : Site → CrossoverPorts V) (origin : Site → Cell) (scale : Int)
    (common : Site → Cell)
    (all : ∀ site∈sites, ∀ role, offset (scopedCrossoverVariableMap site (ports site) role)=common site) :
    UniformOffsets offset (crossoverFamily sites ports origin scale) := by
  intro clause member
  obtain ⟨site,siteMember,clauseMember⟩ := List.mem_flatMap.mp member
  obtain ⟨original,_,clauseEq⟩ := List.mem_map.mp clauseMember
  subst clause
  refine ⟨common site,?_⟩
  intro literal hl
  obtain ⟨renamedLiteral,renamedMember,literalEq⟩ := List.mem_map.mp hl
  subst literal
  obtain ⟨oldLiteral,_,renamedEq⟩ := List.mem_map.mp renamedMember
  subst renamedLiteral
  exact all site siteMember oldLiteral.1

end LeanTrominoes.PlanarThreeSAT
