/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeClauseComputability

/-!
# Computability of the complete periodic 1-in-3SAT reduction

The clause-local primitive-recursive construction is mapped over the indexed
source formula.  Composing this transformation with the verified Wang-to-
periodic-3SAT-3 reduction gives a computable co-r.e.-hardness reduction to
local periodic 1-in-3SAT-3.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThree

/-- The complete exact-one conversion is primitive recursive. -/
theorem formula_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (formula :
      PeriodicCNF Variable →
        PeriodicCNF (OneInThreeVariable Variable)) := by
  have tagged : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicCNF.equivData_primrec
  have one : Primrec₂ fun (_source : PeriodicCNF Variable)
      (taggedClause : PeriodicClause Variable × Nat) =>
      clauseClauses taggedClause.2 taggedClause.1 := by
    change Primrec fun combined :
        PeriodicCNF Variable × (PeriodicClause Variable × Nat) =>
      clauseClauses combined.2.2 combined.2.1
    exact clauseClauses_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
  have clauses : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.zipIdx.flatMap fun taggedClause =>
        clauseClauses taggedClause.2 taggedClause.1 :=
    Primrec.list_flatMap tagged one
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq
    fun _ => rfl

/-- The complete exact-one conversion is computable. -/
theorem formula_computable {Variable : Type*} [Primcodable Variable] :
    Computable (formula :
      PeriodicCNF Variable →
        PeriodicCNF (OneInThreeVariable Variable)) :=
  formula_primrec.to_comp

/-- The variable type at the Wang-to-periodic-1-in-3SAT-3 endpoint. -/
abbrev WangOneInThreeVariable :=
  OneInThreeVariable PeriodicThreeSATThree.WangThreeSATThreeVariable

local instance sourceDecidableEq :
    DecidableEq PeriodicThreeSATThree.WangThreeSATThreeVariable :=
  Classical.decEq _

local instance auxiliaryBEq : BEq OneInThreeAux :=
  instBEqOfDecidableEq

/-- The local periodic 1-in-3SAT-3 decision predicate.  Presentations that
violate locality, width three, or the three-occurrence bound are treated as
no-instances. -/
def LocalOneInThreeSATThreeHolds
    (oneInThree : PeriodicCNF WangOneInThreeVariable) : Prop :=
  oneInThree.IsLocal ∧
    oneInThree.WidthAtMost 3 ∧
    oneInThree.OccurrencesAtMost 3 ∧
    Satisfiable oneInThree

/-- The Wang encoding followed by the 3SAT-3 and exact-one conversions. -/
def wangFormula (tiles : LeanWang.TileSet) :
    PeriodicCNF WangOneInThreeVariable :=
  formula (PeriodicThreeSATThree.wangFormula tiles)

theorem wangFormula_computable : Computable wangFormula :=
  formula_computable.comp PeriodicThreeSATThree.wangFormula_computable

/-- The complete Wang reduction satisfies the exact local periodic
1-in-3SAT-3 endpoint. -/
theorem wangFormula_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔
      LocalOneInThreeSATThreeHolds (wangFormula tiles) := by
  constructor
  · intro tilesPlane
    have sourceHolds :=
      (PeriodicThreeSATThree.wangFormula_correct tiles).1 tilesPlane
    have sourceOccurrences :
        @PeriodicCNF.OccurrencesAtMost
          PeriodicThreeSATThree.WangThreeSATThreeVariable
          instBEqOfDecidableEq (by infer_instance) 3
          (PeriodicThreeSATThree.wangFormula tiles) :=
      PeriodicCNF.occurrencesAtMost_congr_beq
        _ instBEqOfDecidableEq
        (by infer_instance) (by infer_instance) 3
        (PeriodicThreeSATThree.wangFormula tiles)
        sourceHolds.2.2.1
    have generatedOccurrences :=
      formula_occurrencesAtMostThree
        (PeriodicThreeSATThree.wangFormula tiles)
        sourceHolds.2.1 sourceOccurrences
    refine ⟨formula_isLocal sourceHolds.1,
      formula_widthAtMostThree _,
      PeriodicCNF.occurrencesAtMost_congr_beq
        _ _ (by infer_instance) (by infer_instance) 3
        (wangFormula tiles) generatedOccurrences, ?_⟩
    exact (satisfiable_iff _ sourceHolds.2.1).1
      sourceHolds.2.2.2
  · intro targetHolds
    apply (PeriodicThreeSATThree.wangFormula_correct tiles).2
    let source := PeriodicThreeSATThree.wangFormula tiles
    have sourceWidth : source.WidthAtMost 3 :=
      PeriodicThreeSATThree.formula_widthAtMostThree
        (PeriodicThreeCNF.formula_widthAtMostThree
          (WangPeriodicCNF.formula tiles))
    refine ⟨PeriodicThreeSATThree.formula_isLocal
        (PeriodicThreeCNF.formula_isLocal
          (WangPeriodicCNF.formula_isLocal tiles)),
      sourceWidth,
      PeriodicThreeSATThree.formula_occurrencesAtMostThree
        (PeriodicThreeCNF.wangFormula tiles), ?_⟩
    exact (satisfiable_iff source sourceWidth).2
      targetHolds.2.2.2

/-- Local periodic 1-in-3SAT-3 satisfiability is co-r.e.-hard. -/
theorem localOneInThreeSATThreeCoREHard :
    LeanWang.CoREHard LocalOneInThreeSATThreeHolds := by
  intro α _ source sourceCoRE
  obtain ⟨reduce, reduceComputable, reduceCorrect⟩ :=
    LeanWang.domino_problem_coRE_hard source sourceCoRE
  refine ⟨wangFormula ∘ reduce,
    wangFormula_computable.comp reduceComputable, ?_⟩
  intro input
  rw [reduceCorrect input]
  exact wangFormula_correct (reduce input)

end PeriodicOneInThree
end LeanTrominoes
