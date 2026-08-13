/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMEncodedDegree

/-!
# Co-r.e.-hardness of restricted periodic 3DM

The verified Wang-to-local-exact-one reduction is composed with unit
elimination and the natural-number periodic 3DM encoding.  Every resulting
instance is well formed and every colored element has degree two or three.
-/

noncomputable section

namespace LeanTrominoes

/-- The restricted periodic 3DM decision predicate reached by the reduction. -/
def PeriodicThreeDMTwoOrThreeHolds
    (problem : PeriodicThreeDM) : Prop :=
  problem.IsWellFormed ∧
    problem.DegreeTwoOrThree ∧
    problem.Satisfiable

/-- The equivalent abstract trichromatic-orientation decision predicate. -/
def PeriodicTrichromaticOrientationTwoOrThreeHolds
    (problem : PeriodicThreeDM) : Prop :=
  problem.IsWellFormed ∧
    problem.DegreeTwoOrThree ∧
    problem.HasOrientation

namespace PeriodicOneInThreeToThreeDM

local instance sourceDecidableEq :
    DecidableEq
      PeriodicThreeSATThree.WangThreeSATThreeVariable :=
  Classical.decEq _

local instance auxiliaryBEq : BEq OneInThreeAux :=
  instBEqOfDecidableEq

local instance wangVariableDecidableEq :
    DecidableEq PeriodicOneInThree.WangOneInThreeVariable :=
  Classical.decEq _

/-- The complete Wang-to-periodic-3DM map. -/
def wangEncodedProblem (tiles : LeanWang.TileSet) :
    PeriodicThreeDM :=
  unitFreeEncodedProblem
    (PeriodicOneInThree.wangFormula tiles)

theorem wangEncodedProblem_computable :
    Computable wangEncodedProblem :=
  unitFreeEncodedProblem_computable.comp
    PeriodicOneInThree.wangFormula_computable

/-- The exact-one Wang endpoint has width at most three independently of
satisfiability. -/
theorem wangFormula_widthAtMostThree
    (tiles : LeanWang.TileSet) :
    (PeriodicOneInThree.wangFormula tiles).WidthAtMost 3 :=
  PeriodicOneInThree.formula_widthAtMostThree _

/-- The exact-one Wang endpoint is local independently of satisfiability. -/
theorem wangFormula_isLocal (tiles : LeanWang.TileSet) :
    (PeriodicOneInThree.wangFormula tiles).IsLocal := by
  exact PeriodicOneInThree.formula_isLocal
    (PeriodicThreeSATThree.formula_isLocal
      (PeriodicThreeCNF.formula_isLocal
        (WangPeriodicCNF.formula_isLocal tiles)))

/-- The exact-one Wang endpoint has at most three syntactic occurrences of
every protovariable independently of satisfiability. -/
theorem wangFormula_occurrencesAtMostThree
    (tiles : LeanWang.TileSet) :
    @PeriodicCNF.OccurrencesAtMost
      PeriodicOneInThree.WangOneInThreeVariable
      instBEqOfDecidableEq (by infer_instance) 3
      (PeriodicOneInThree.wangFormula tiles) := by
  let source := PeriodicThreeSATThree.wangFormula tiles
  have sourceWidth : source.WidthAtMost 3 :=
    PeriodicThreeSATThree.formula_widthAtMostThree
      (PeriodicThreeCNF.formula_widthAtMostThree
        (WangPeriodicCNF.formula tiles))
  have sourceOccurrences :=
    PeriodicThreeSATThree.formula_occurrencesAtMostThree
      (PeriodicThreeCNF.wangFormula tiles)
  have sourceOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        PeriodicThreeSATThree.WangThreeSATThreeVariable
        instBEqOfDecidableEq (by infer_instance) 3 source :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ instBEqOfDecidableEq
      (by infer_instance) (by infer_instance) 3 source
      sourceOccurrences
  have generatedOccurrences :=
    PeriodicOneInThree.formula_occurrencesAtMostThree
      source sourceWidth sourceOccurrences'
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ instBEqOfDecidableEq
    (by infer_instance) (by infer_instance) 3
    (PeriodicOneInThree.wangFormula tiles)
    generatedOccurrences

/-- Wang tiles tile the plane exactly when the complete restricted periodic
3DM output has a perfect matching. -/
theorem wangEncodedProblem_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔
      PeriodicThreeDMTwoOrThreeHolds
        (wangEncodedProblem tiles) := by
  let source := PeriodicOneInThree.wangFormula tiles
  have width : source.WidthAtMost 3 :=
    wangFormula_widthAtMostThree tiles
  have occurrences :
      @PeriodicCNF.OccurrencesAtMost
        PeriodicOneInThree.WangOneInThreeVariable
        instBEqOfDecidableEq (by infer_instance) 3 source :=
    wangFormula_occurrencesAtMostThree tiles
  constructor
  · intro tilesPlane
    have sourceHolds :=
      (PeriodicOneInThree.wangFormula_correct tiles).1
        tilesPlane
    refine
      ⟨encodedProblem_isWellFormed
          (PeriodicOneInThreeNoUnits.formula source),
        unitFreeEncodedProblem_degreeTwoOrThree
          source occurrences width,
        ?_⟩
    exact
      (unitFreeEncodedProblem_satisfiable_iff
        source occurrences).2 sourceHolds.2.2.2
  · rintro ⟨_wellFormed, _degree, matching⟩
    apply (PeriodicOneInThree.wangFormula_correct tiles).2
    refine
      ⟨wangFormula_isLocal tiles, width, ?_,
        (unitFreeEncodedProblem_satisfiable_iff
          source occurrences).1 matching⟩
    exact PeriodicCNF.occurrencesAtMost_congr_beq
      instBEqOfDecidableEq _
      (by infer_instance) (by infer_instance) 3 source
      occurrences

/-- Wang tiles tile the plane exactly when the corresponding abstract
trichromatic incidence graph has a valid orientation. -/
theorem wangEncodedProblem_orientation_correct
    (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔
      PeriodicTrichromaticOrientationTwoOrThreeHolds
        (wangEncodedProblem tiles) := by
  rw [wangEncodedProblem_correct]
  unfold PeriodicThreeDMTwoOrThreeHolds
    PeriodicTrichromaticOrientationTwoOrThreeHolds
  constructor
  · rintro ⟨wellFormed, degree, matching⟩
    exact
      ⟨wellFormed, degree,
        (PeriodicThreeDM.satisfiable_iff_hasOrientation
          (wangEncodedProblem tiles)).1 matching⟩
  · rintro ⟨wellFormed, degree, orientation⟩
    exact
      ⟨wellFormed, degree,
        (PeriodicThreeDM.satisfiable_iff_hasOrientation
          (wangEncodedProblem tiles)).2 orientation⟩

/-- Well-formed periodic 3DM with colored degree two or three is
co-r.e.-hard. -/
theorem periodicThreeDMTwoOrThreeCoREHard :
    LeanWang.CoREHard PeriodicThreeDMTwoOrThreeHolds := by
  intro α _ source sourceCoRE
  obtain ⟨reduce, reduceComputable, reduceCorrect⟩ :=
    LeanWang.domino_problem_coRE_hard source sourceCoRE
  refine
    ⟨wangEncodedProblem ∘ reduce,
      wangEncodedProblem_computable.comp reduceComputable,
      ?_⟩
  intro input
  rw [reduceCorrect input]
  exact wangEncodedProblem_correct (reduce input)

/-- The associated abstract trichromatic orientation problem with colored
degree two or three is co-r.e.-hard. -/
theorem periodicTrichromaticOrientationTwoOrThreeCoREHard :
    LeanWang.CoREHard
      PeriodicTrichromaticOrientationTwoOrThreeHolds := by
  intro α _ source sourceCoRE
  obtain ⟨reduce, reduceComputable, reduceCorrect⟩ :=
    LeanWang.domino_problem_coRE_hard source sourceCoRE
  refine
    ⟨wangEncodedProblem ∘ reduce,
      wangEncodedProblem_computable.comp reduceComputable,
      ?_⟩
  intro input
  rw [reduceCorrect input]
  exact wangEncodedProblem_orientation_correct
    (reduce input)

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
