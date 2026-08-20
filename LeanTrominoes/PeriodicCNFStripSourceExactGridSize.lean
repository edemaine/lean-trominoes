/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicThreeCNFExactSize
import LeanTrominoes.PeriodicThreeSATThreeExactDrawingSize

/-! # Exact source grid size for an admissible width-three formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

local instance sourceExactGridVariableDecidableEq : DecidableEq Variable :=
  Classical.decEq _

/-- On an admissible input already of width three, guarded normalization and
occurrence splitting give the exact generic orthocrossing scale below. -/
theorem drawingGridSize_incidenceGraph_sourceFormula_of
    (source : PeriodicCNF Nat)
    (admissible : SourceAdmissible source)
    (width : source.WidthAtMost 3) :
    PeriodicOrthocrossing.drawingGridSize
        (PeriodicCNF.incidenceGraph (sourceFormula source)) =
      16 * (source.clauses.length +
        5 * PeriodicCNF.presentationLiteralCount source + 1) := by
  rw [sourceFormula, if_pos admissible]
  unfold normalizedFormula
  rw [PeriodicThreeSATThree.drawingGridSize_incidenceGraph_formula]
  rw [PeriodicThreeCNF.formula_clauses_length_of_widthAtMostThree
      source width,
    PeriodicThreeCNF.formula_presentationLiteralCount_of_widthAtMostThree
      source width]

end PeriodicCNFStripReduction
end LeanTrominoes
