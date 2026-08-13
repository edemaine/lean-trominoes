/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarOneInThreeFigureNineInstantiation
import LeanTrominoes.PlanarOneInThreeNoUnitsInstantiation
import LeanTrominoes.PositionedPeriodicCNFScaling

/-!
# Atom distinctness in the local exact-one replacements

The finite drawing instantiations require different present boundary roles to
name different atoms.  Figure 9 automatically gives every generated clause
that property: each core clause contains one source atom and two differently
named fresh auxiliaries, while each forced-padding clause is a unit.

This file packages the per-clause property and proves that automatic
downstream half of the distinctness obligation.
-/

namespace LeanTrominoes

namespace PlanarThreeSAT.EmbeddedClause

/-- No variable atom is repeated within an embedded clause. -/
def AtomsNodup {Variable : Type*} [DecidableEq Variable]
    (clause : EmbeddedClause Variable) : Prop :=
  (clause.literals.map Prod.fst).Nodup

end PlanarThreeSAT.EmbeddedClause

namespace PositionedPeriodicClause

/-- No variable atom is repeated within a positioned periodic clause. -/
def AtomsNodup {Variable : Type*} [DecidableEq Variable]
    (clause : PositionedPeriodicClause Variable) : Prop :=
  (clause.literals.map PeriodicLiteral.atom).Nodup

end PositionedPeriodicClause

namespace PositionedPeriodicCNF

/-- Every clause in a positioned periodic formula has distinct atoms. -/
def AllAtomsNodup {Variable : Type*} [DecidableEq Variable]
    (formula : PositionedPeriodicCNF Variable) : Prop :=
  ∀ clause ∈ formula.clauses, clause.AtomsNodup

/-- Injective variable renaming preserves per-clause atom distinctness. -/
theorem allAtomsNodup_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    {formula : PositionedPeriodicCNF Source}
    (distinct : formula.AllAtomsNodup) :
    (formula.rename variableMap).AllAtomsNodup := by
  intro renamedClause renamedMember
  unfold PositionedPeriodicCNF.rename at renamedMember
  rcases List.mem_map.mp renamedMember with
    ⟨sourceClause, sourceMember, renamedEqual⟩
  subst renamedClause
  have sourceDistinct := distinct sourceClause sourceMember
  unfold PositionedPeriodicClause.AtomsNodup at sourceDistinct ⊢
  rw [List.map_map]
  simpa [Function.comp_def] using
    sourceDistinct.map injective

/-- Uniform coordinate scaling preserves per-clause atom distinctness,
because it leaves every clause's literal list unchanged. -/
theorem AllAtomsNodup.scale
    {Variable : Type*} [DecidableEq Variable]
    {formula : PositionedPeriodicCNF Variable}
    (distinct : formula.AllAtomsNodup)
    (factor : Nat) :
    (formula.scale factor).AllAtomsNodup := by
  intro scaledClause scaledClauseMember
  rw [scale_clauses] at scaledClauseMember
  rcases List.mem_map.mp scaledClauseMember with
    ⟨clause, clauseMember, rfl⟩
  simpa [PositionedPeriodicClause.AtomsNodup] using
    distinct clause clauseMember

end PositionedPeriodicCNF

namespace PlanarOneInThree

open PlanarThreeSAT

/-- Every semantic Figure 9 clause has pairwise distinct atoms. -/
theorem PeriodicOneInThree.clauseClauses_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PeriodicClause Variable) :
    ∀ generated ∈
        PeriodicOneInThree.clauseClauses clauseIndex source,
      (generated.map PeriodicLiteral.atom).Nodup := by
  intro generated generatedMember
  rcases source with _ | ⟨first, rest⟩
  · simp only [PeriodicOneInThree.clauseClauses,
      PeriodicOneInThree.disjunctionGadget,
      List.mem_cons, List.mem_append, List.mem_nil_iff,
      or_false] at generatedMember
    rcases generatedMember with
      (rfl | rfl | rfl) | rfl | rfl | rfl <;>
      simp [PeriodicOneInThree.padding,
        PeriodicOneInThree.forcePaddingFalse,
        PeriodicOneInThree.auxiliary,
        PeriodicOneInThree.negate]
  · rcases rest with _ | ⟨second, rest⟩
    · simp only [PeriodicOneInThree.clauseClauses,
        PeriodicOneInThree.disjunctionGadget,
        List.mem_cons, List.mem_append, List.mem_nil_iff,
        or_false] at generatedMember
      rcases generatedMember with
        (rfl | rfl | rfl) | rfl | rfl <;>
        simp [PeriodicOneInThree.padding,
          PeriodicOneInThree.forcePaddingFalse,
          PeriodicOneInThree.auxiliary,
          PeriodicOneInThree.liftLiteral,
          PeriodicOneInThree.negate]
    · rcases rest with _ | ⟨third, rest⟩
      · simp only [PeriodicOneInThree.clauseClauses,
          PeriodicOneInThree.disjunctionGadget,
          List.mem_cons, List.mem_append, List.mem_nil_iff,
          or_false] at generatedMember
        rcases generatedMember with
          (rfl | rfl | rfl) | rfl <;>
          simp [PeriodicOneInThree.padding,
            PeriodicOneInThree.forcePaddingFalse,
            PeriodicOneInThree.auxiliary,
            PeriodicOneInThree.liftLiteral,
            PeriodicOneInThree.negate]
      · simp only [PeriodicOneInThree.clauseClauses,
          PeriodicOneInThree.disjunctionGadget,
          List.mem_cons, List.mem_nil_iff, or_false]
          at generatedMember
        rcases generatedMember with rfl | rfl | rfl <;>
          simp [PeriodicOneInThree.auxiliary,
            PeriodicOneInThree.liftLiteral,
            PeriodicOneInThree.negate]

/-- Every clause generated by Figure 9 has pairwise distinct variable
atoms, independently of the source clause's own repetitions. -/
theorem clauseGadget_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable) :
    ∀ generated ∈ clauseGadget clauseIndex source,
      generated.AtomsNodup := by
  intro generated generatedMember
  unfold clauseGadget at generatedMember
  rcases List.mem_map.mp generatedMember with
    ⟨taggedClause, taggedClauseMember, generatedEqual⟩
  subst generated
  have atomsNodup :=
    PeriodicOneInThree.clauseClauses_atomsNodup
      clauseIndex (zeroOffsetClause source)
      taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)
  simpa [EmbeddedClause.AtomsNodup,
    embedGeneratedClause, List.map_map,
    Function.comp_def] using atomsNodup

end PlanarOneInThree

namespace PeriodicOneInThreePositioned

/-- Every positioned Figure 9 clause has pairwise distinct atoms. -/
theorem clauseGadget_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    ∀ generated ∈ clauseGadget clauseIndex source,
      generated.AtomsNodup := by
  intro generated generatedMember
  unfold clauseGadget at generatedMember
  rcases List.mem_map.mp generatedMember with
    ⟨taggedClause, taggedMember, generatedEqual⟩
  subst generated
  exact
    PlanarOneInThree.PeriodicOneInThree.clauseClauses_atomsNodup
      clauseIndex source.literals taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedMember)

/-- The complete positioned Figure 9 output has distinct atoms in every
generated clause. -/
theorem formula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) :
    (formula source).AllAtomsNodup := by
  intro generated generatedMember
  unfold formula at generatedMember
  rcases List.mem_flatMap.mp generatedMember with
    ⟨taggedSource, _taggedSourceMember,
      generatedMember⟩
  exact clauseGadget_atomsNodup
    taggedSource.2 taggedSource.1
    generated generatedMember

end PeriodicOneInThreePositioned

namespace PeriodicOneInThreeNoUnits

/-- Unit elimination preserves atom distinctness in every generated clause.
The only inherited case is a retained source clause of arity at least two. -/
theorem clauseClauses_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (sourceDistinct :
      (source.map PeriodicLiteral.atom).Nodup) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      (generated.map PeriodicLiteral.atom).Nodup := by
  intro generated generatedMember
  rcases source with _ | ⟨first, rest⟩
  · simp only [clauseClauses, List.mem_cons,
      List.mem_nil_iff, or_false] at generatedMember
    rcases generatedMember with rfl | rfl | rfl <;>
      simp [auxiliary]
  · rcases rest with _ | ⟨second, rest⟩
    · simp only [clauseClauses, List.mem_cons,
        List.mem_nil_iff, or_false] at generatedMember
      rcases generatedMember with rfl | rfl <;>
        simp [auxiliary, liftLiteral,
          PeriodicOneInThree.negate]
    · simp only [clauseClauses, List.mem_singleton]
        at generatedMember
      subst generated
      rw [List.map_map]
      simpa [Function.comp_def, liftLiteral] using
        sourceDistinct.map
          (by
            intro left right equal
            exact Sum.inl.inj equal :
            Function.Injective (@Sum.inl
              Variable
              ((Nat × PeriodicClause Variable) ×
                OneInThreeNoUnitAux)))

end PeriodicOneInThreeNoUnits

namespace PeriodicOneInThreeNoUnitsPositioned

/-- One positioned unit-elimination gadget preserves atom distinctness. -/
theorem clauseGadget_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (sourceDistinct : source.AtomsNodup) :
    ∀ generated ∈ clauseGadget clauseIndex source,
      generated.AtomsNodup := by
  intro generated generatedMember
  unfold clauseGadget at generatedMember
  rcases List.mem_map.mp generatedMember with
    ⟨taggedClause, taggedMember, generatedEqual⟩
  subst generated
  exact
    PeriodicOneInThreeNoUnits.clauseClauses_atomsNodup
      clauseIndex source.literals sourceDistinct
      taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedMember)

/-- Unit elimination preserves atom distinctness throughout a positioned
formula. -/
theorem formula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceDistinct : source.AllAtomsNodup) :
    (formula source).AllAtomsNodup := by
  intro generated generatedMember
  unfold formula at generatedMember
  rcases List.mem_flatMap.mp generatedMember with
    ⟨taggedSource, taggedSourceMember,
      generatedMember⟩
  exact clauseGadget_atomsNodup
    taggedSource.2 taggedSource.1
    (sourceDistinct taggedSource.1
      (List.fst_mem_of_mem_zipIdx taggedSourceMember))
    generated generatedMember

end PeriodicOneInThreeNoUnitsPositioned

end LeanTrominoes
