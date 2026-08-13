/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATWires

/-!
# Width bounds for embedded planar SAT gadgets

The positioned gadget layer stores geometry in `EmbeddedClause.position`, but
clause width depends only on its literal list.  This file supplies the small
compositional library needed to certify that every Figure 8 clause, equality
wire, and duplicator has width at most three.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

namespace EmbeddedClause

/-- An embedded clause contains at most `width` literal occurrences. -/
def WidthAtMost {Variable : Type*}
    (width : Nat) (clause : EmbeddedClause Variable) : Prop :=
  clause.literals.length ≤ width

instance {Variable : Type*} (width : Nat)
    (clause : EmbeddedClause Variable) :
    Decidable (clause.WidthAtMost width) := by
  unfold WidthAtMost
  infer_instance

/-- Renaming variables and moving a clause preserve its width. -/
@[simp]
theorem map_widthAtMost_iff {Source Target : Type*}
    (width : Nat) (variableMap : Source → Target)
    (positionMap : Cell → Cell) (clause : EmbeddedClause Source) :
    (clause.map variableMap positionMap).WidthAtMost width ↔
      clause.WidthAtMost width := by
  simp [WidthAtMost, EmbeddedClause.map]

end EmbeddedClause

/-- Every clause in an embedded formula has the requested width. -/
def FormulaWidthAtMost {Variable : Type*}
    (width : Nat) (formula : List (EmbeddedClause Variable)) : Prop :=
  ∀ clause ∈ formula, clause.WidthAtMost width

instance {Variable : Type*} (width : Nat)
    (formula : List (EmbeddedClause Variable)) :
    Decidable (FormulaWidthAtMost width formula) := by
  unfold FormulaWidthAtMost
  infer_instance

/-- Formula width is preserved by uniform variable and position maps. -/
theorem formulaWidthAtMost_map_iff {Source Target : Type*}
    (width : Nat) (variableMap : Source → Target)
    (positionMap : Cell → Cell)
    (formula : List (EmbeddedClause Source)) :
    FormulaWidthAtMost width
        (formula.map fun clause =>
          clause.map variableMap positionMap) ↔
      FormulaWidthAtMost width formula := by
  constructor
  · intro mappedWidth clause clauseMem
    apply
      (EmbeddedClause.map_widthAtMost_iff
        width variableMap positionMap clause).mp
    exact mappedWidth (clause.map variableMap positionMap)
      (List.mem_map.mpr ⟨clause, clauseMem, rfl⟩)
  · intro sourceWidth mappedClause mappedMem
    rcases List.mem_map.mp mappedMem with
      ⟨clause, clauseMem, mappedEq⟩
    subst mappedClause
    apply
      (EmbeddedClause.map_widthAtMost_iff
        width variableMap positionMap clause).mpr
    exact sourceWidth clause clauseMem

/-- Formula width distributes over concatenation. -/
theorem formulaWidthAtMost_append_iff {Variable : Type*}
    (width : Nat)
    (first second : List (EmbeddedClause Variable)) :
    FormulaWidthAtMost width (first ++ second) ↔
      FormulaWidthAtMost width first ∧
        FormulaWidthAtMost width second := by
  constructor
  · intro combined
    constructor
    · intro clause clauseMem
      exact combined clause
        (List.mem_append_left second clauseMem)
    · intro clause clauseMem
      exact combined clause
        (List.mem_append_right first clauseMem)
  · rintro ⟨firstWidth, secondWidth⟩ clause clauseMem
    rcases List.mem_append.mp clauseMem with
      clauseMem | clauseMem
    · exact firstWidth clause clauseMem
    · exact secondWidth clause clauseMem

/-- A concatenated family has bounded width exactly when every member
formula does. -/
theorem formulaWidthAtMost_flatMap_iff
    {Site Variable : Type*}
    (width : Nat) (sites : List Site)
    (formulaAt : Site → List (EmbeddedClause Variable)) :
    FormulaWidthAtMost width (sites.flatMap formulaAt) ↔
      ∀ site ∈ sites,
        FormulaWidthAtMost width (formulaAt site) := by
  constructor
  · intro combined site siteMem clause clauseMem
    exact combined clause
      (List.mem_flatMap.mpr ⟨site, siteMem, clauseMem⟩)
  · intro members clause clauseMem
    rcases List.mem_flatMap.mp clauseMem with
      ⟨site, siteMem, clauseMem⟩
    exact members site siteMem clause clauseMem

/-- Every clause of the fixed Figure 8 crossover has width at most three. -/
theorem crossoverFormula_widthAtMostThree :
    FormulaWidthAtMost 3 crossoverFormula := by
  native_decide

/-- Every clause of the fixed Figure 8 duplicator is binary. -/
theorem duplicatorFormula_widthAtMostThree :
    FormulaWidthAtMost 3 duplicatorFormula := by
  native_decide

/-- Affine placement and renaming preserve a formula width bound. -/
theorem instantiateFormula_widthAtMost
    {Source Target : Type*}
    (width : Nat) (variableMap : Source → Target)
    (origin : Cell) (scale : Int)
    (source : List (EmbeddedClause Source))
    (sourceWidth : FormulaWidthAtMost width source) :
    FormulaWidthAtMost width
      (instantiateFormula variableMap origin scale source) := by
  intro targetClause targetMem
  rcases List.mem_map.mp targetMem with
    ⟨sourceClause, sourceMem, targetEq⟩
  subst targetClause
  simpa [EmbeddedClause.WidthAtMost,
    EmbeddedClause.rename, EmbeddedClause.place,
    EmbeddedClause.map] using
      sourceWidth sourceClause sourceMem

/-- One scoped and positioned crossover has width at most three. -/
theorem scopedCrossoverInstance_widthAtMostThree
    {Site Variable : Type*}
    (site : Site) (ports : CrossoverPorts Variable)
    (origin : Cell) (scale : Int) :
    FormulaWidthAtMost 3
      (scopedCrossoverInstance site ports origin scale) := by
  exact instantiateFormula_widthAtMost 3
    (scopedCrossoverVariableMap site ports)
    origin scale crossoverFormula
    crossoverFormula_widthAtMostThree

/-- Any finite family of positioned crossovers has width at most three. -/
theorem crossoverFamily_widthAtMostThree
    {Site Variable : Type*}
    (sites : List Site)
    (ports : Site → CrossoverPorts Variable)
    (origin : Site → Cell) (scale : Int) :
    FormulaWidthAtMost 3
      (crossoverFamily sites ports origin scale) := by
  apply
    (formulaWidthAtMost_flatMap_iff 3 sites
      (fun site =>
        scopedCrossoverInstance site (ports site)
          (origin site) scale)).mpr
  intro site _siteMem
  exact scopedCrossoverInstance_widthAtMostThree
    site (ports site) (origin site) scale

/-- One positioned duplicator has width at most three. -/
theorem duplicatorInstance_widthAtMostThree
    {Variable : Type*}
    (ports : DuplicatorPorts Variable)
    (origin : Cell) (scale : Int) :
    FormulaWidthAtMost 3
      (duplicatorInstance ports origin scale) := by
  exact instantiateFormula_widthAtMost 3
    (duplicatorVariableMap ports)
    origin scale duplicatorFormula
    duplicatorFormula_widthAtMostThree

/-- Any finite family of positioned duplicators has width at most three. -/
theorem duplicatorFamily_widthAtMostThree
    {Site Variable : Type*}
    (sites : List Site)
    (ports : Site → DuplicatorPorts Variable)
    (origin : Site → Cell) (scale : Int) :
    FormulaWidthAtMost 3
      (duplicatorFamily sites ports origin scale) := by
  apply
    (formulaWidthAtMost_flatMap_iff 3 sites
      (fun site =>
        duplicatorInstance (ports site) (origin site) scale)).mpr
  intro site _siteMem
  exact duplicatorInstance_widthAtMostThree
    (ports site) (origin site) scale

/-- Each equality link consists of two binary clauses. -/
theorem equalityInstance_widthAtMostThree
    {Variable : Type*}
    (first second : Variable) (positions : EqualityPositions) :
    FormulaWidthAtMost 3
      (equalityInstance first second positions) := by
  simp [FormulaWidthAtMost, EmbeddedClause.WidthAtMost,
    equalityInstance]

/-- Any finite equality-wire family has width at most three. -/
theorem equalityFamily_widthAtMostThree
    {Variable : Type*}
    (links : List (EqualityLink Variable)) :
    FormulaWidthAtMost 3 (equalityFamily links) := by
  apply
    (formulaWidthAtMost_flatMap_iff 3 links
      (fun link =>
        equalityInstance link.first link.second
          link.positions)).mpr
  intro link _linkMem
  exact equalityInstance_widthAtMostThree
    link.first link.second link.positions

end PlanarThreeSAT
end LeanTrominoes
