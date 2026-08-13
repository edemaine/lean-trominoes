/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.WangPeriodicCNF
import LeanWang.Final

/-!
# Computability of the Wang-to-periodic-CNF reduction

The semantic encoding in `WangPeriodicCNF` is implemented entirely by
primitive-recursive list operations.  This file verifies that fact and
packages the first many-one reduction in the hardness chain.
-/

noncomputable section

namespace LeanTrominoes
namespace WangPeriodicCNF

open LeanWang

theorem positive_primrec : Primrec₂ positive := by
  change Primrec fun input : WangTile × Cell =>
    positive input.1 input.2
  exact (PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair Primrec.snd (Primrec.const true)))).of_eq fun _ => rfl

theorem negative_primrec : Primrec₂ negative := by
  change Primrec fun input : WangTile × Cell =>
    negative input.1 input.2
  exact (PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair Primrec.snd (Primrec.const false)))).of_eq fun _ => rfl

theorem orderedPairs_primrec : Primrec orderedPairs := by
  have row : Primrec₂ fun (tiles : TileSet) (first : WangTile) =>
      tiles.map fun second => (first, second) := by
    change Primrec fun input : TileSet × WangTile =>
      input.1.map fun second => (input.2, second)
    exact Primrec.list_map Primrec.fst
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_flatMap Primrec.id row

theorem atLeastOneClause_primrec : Primrec atLeastOneClause := by
  have literal : Primrec₂ fun (_tiles : TileSet) (tile : WangTile) =>
      positive tile here := by
    change Primrec fun input : TileSet × WangTile =>
      positive input.2 here
    exact positive_primrec.comp Primrec.snd (Primrec.const here)
  exact Primrec.list_map Primrec.id literal

private theorem horizontalOption_primrec :
    Primrec fun pair : WangTile × WangTile =>
      if WangTile.HMatches pair.1 pair.2 then
        none
      else
        some [negative pair.1 here, negative pair.2 east] := by
  have compatible : PrimrecPred fun pair : WangTile × WangTile =>
      WangTile.HMatches pair.1 pair.2 := by
    exact Primrec.eq.comp
      (WangTile.e_primrec.comp Primrec.fst)
      (WangTile.w_primrec.comp Primrec.snd)
  have leftLiteral : Primrec fun pair : WangTile × WangTile =>
      negative pair.1 here :=
    negative_primrec.comp Primrec.fst (Primrec.const here)
  have rightLiteral : Primrec fun pair : WangTile × WangTile =>
      negative pair.2 east :=
    negative_primrec.comp Primrec.snd (Primrec.const east)
  have clause : Primrec fun pair : WangTile × WangTile =>
      [negative pair.1 here, negative pair.2 east] :=
    Primrec.list_cons.comp leftLiteral
      (Primrec.list_cons.comp rightLiteral (Primrec.const []))
  exact Primrec.ite compatible (Primrec.const none)
    (Primrec.option_some.comp clause)

theorem horizontalClauses_primrec : Primrec horizontalClauses := by
  have option : Primrec₂ fun (_tiles : TileSet) (pair : WangTile × WangTile) =>
      if WangTile.HMatches pair.1 pair.2 then
        none
      else
        some [negative pair.1 here, negative pair.2 east] := by
    exact horizontalOption_primrec.comp Primrec.snd
  exact Primrec.listFilterMap orderedPairs_primrec option

private theorem verticalOption_primrec :
    Primrec fun pair : WangTile × WangTile =>
      if WangTile.VMatches pair.1 pair.2 then
        none
      else
        some [negative pair.1 here, negative pair.2 north] := by
  have compatible : PrimrecPred fun pair : WangTile × WangTile =>
      WangTile.VMatches pair.1 pair.2 := by
    exact Primrec.eq.comp
      (WangTile.n_primrec.comp Primrec.fst)
      (WangTile.s_primrec.comp Primrec.snd)
  have lowerLiteral : Primrec fun pair : WangTile × WangTile =>
      negative pair.1 here :=
    negative_primrec.comp Primrec.fst (Primrec.const here)
  have upperLiteral : Primrec fun pair : WangTile × WangTile =>
      negative pair.2 north :=
    negative_primrec.comp Primrec.snd (Primrec.const north)
  have clause : Primrec fun pair : WangTile × WangTile =>
      [negative pair.1 here, negative pair.2 north] :=
    Primrec.list_cons.comp lowerLiteral
      (Primrec.list_cons.comp upperLiteral (Primrec.const []))
  exact Primrec.ite compatible (Primrec.const none)
    (Primrec.option_some.comp clause)

theorem verticalClauses_primrec : Primrec verticalClauses := by
  have option : Primrec₂ fun (_tiles : TileSet) (pair : WangTile × WangTile) =>
      if WangTile.VMatches pair.1 pair.2 then
        none
      else
        some [negative pair.1 here, negative pair.2 north] := by
    exact verticalOption_primrec.comp Primrec.snd
  exact Primrec.listFilterMap orderedPairs_primrec option

/-- The complete Wang-to-periodic-CNF translation is primitive recursive. -/
theorem formula_primrec : Primrec formula := by
  have tail : Primrec fun tiles =>
      horizontalClauses tiles ++ verticalClauses tiles :=
    Primrec.list_append.comp horizontalClauses_primrec verticalClauses_primrec
  have clauses : Primrec fun tiles =>
      atLeastOneClause tiles ::
        horizontalClauses tiles ++ verticalClauses tiles :=
    Primrec.list_cons.comp atLeastOneClause_primrec tail
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq fun _ => rfl

theorem formula_computable : Computable formula :=
  formula_primrec.to_comp

/-- Satisfiability for periodic CNF formulas whose atoms are Wang tiles. -/
def Holds (periodicCNF : PeriodicCNF WangTile) : Prop :=
  periodicCNF.Satisfiable

/-- Local periodic CNF satisfiability is already co-r.e.-hard on the restricted
family produced by `formula`. -/
theorem coREHard : LeanWang.CoREHard Holds := by
  intro α _ source source_coRE
  obtain ⟨reduce, reduce_computable, reduce_correct⟩ :=
    LeanWang.domino_problem_coRE_hard source source_coRE
  refine ⟨formula ∘ reduce, formula_computable.comp reduce_computable, ?_⟩
  intro input
  rw [reduce_correct input]
  exact formula_correct (reduce input)

/-- The local periodic-CNF decision predicate, treating nonlocal presentations
as no-instances. -/
def LocalHolds (periodicCNF : PeriodicCNF WangTile) : Prop :=
  periodicCNF.IsLocal ∧ periodicCNF.Satisfiable

/-- Co-r.e.-hardness holds for the actual local source problem, not merely for
unrestricted periodic CNF. -/
theorem localCoREHard : LeanWang.CoREHard LocalHolds := by
  intro α _ source source_coRE
  obtain ⟨reduce, reduce_computable, reduce_correct⟩ :=
    LeanWang.domino_problem_coRE_hard source source_coRE
  refine ⟨formula ∘ reduce, formula_computable.comp reduce_computable, ?_⟩
  intro input
  rw [reduce_correct input]
  constructor
  · intro tilesPlane
    exact ⟨formula_isLocal (reduce input),
      (formula_correct (reduce input)).1 tilesPlane⟩
  · exact fun localHolds =>
      (formula_correct (reduce input)).2 localHolds.2

end WangPeriodicCNF
end LeanTrominoes
