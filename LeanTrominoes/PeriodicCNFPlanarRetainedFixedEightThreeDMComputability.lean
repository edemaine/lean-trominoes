import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplitComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightThreeDM
import LeanTrominoes.PeriodicCNFGaugeComputability
import LeanTrominoes.PeriodicCNFPlanarPeriodicizationComputability
import LeanTrominoes.PeriodicOneInThreeNoUnitsComputability
import LeanTrominoes.PeriodicOneInThreeReductionComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability

/-!
# Computability of the retained fixed-eight 3DM endpoint

The positioned exact-one construction erases to the ordinary Figure 9
reduction, opaque variable wrapping, and unit-clause elimination.  The
normalized 3DM endpoint then depends only on this erased formula: canonical
clause-anchor normalization followed by the planar exact-one-to-3DM encoding.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1200000

/-- The erased retained fixed-eight unit-free exact-one formula is primitive
recursive, without computing its proof-carrying positioned presentation. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase := by
  have exactOne := PeriodicOneInThree.formula_primrec.comp
    (retainedDrawingEightOccurrenceSplitFormula_primrec
      (Variable := Variable))
  have wrapped := wrapPeriodicPlanarSATFormula_primrec.comp exactOne
  have unitFree := PeriodicOneInThreeNoUnits.formula_primrec.comp wrapped
  exact unitFree.of_eq fun source => by
    simpa only [retainedDrawingEightOccurrenceSplitPositionedFormula_erase] using
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase
        source).symm

/-- The named normalized 3DM endpoint is its erased exact-one formula after
canonical clause-anchor normalization and finite 3DM encoding. -/
private theorem retainedFixedEightPeriodicThreeDMProblem_eq_encoded
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    retainedFixedEightPeriodicThreeDMProblem source =
      PeriodicPlanarOneInThreeToThreeDM.encodedProblem
        ((retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).erase.anchorNormalize) := by
  unfold retainedFixedEightPeriodicThreeDMProblem
    PeriodicPlanarOneInThreeToThreeDM.normalizedProblem
  rw [PeriodicPlanarOneInThreeToThreeDM.normalizedSource_eq]

/-- The exact retained fixed-eight normalized periodic 3DM problem is
primitive recursive from the original finite periodic CNF. -/
theorem retainedFixedEightPeriodicThreeDMProblem_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFixedEightPeriodicThreeDMProblem :
      PeriodicCNF Variable → PeriodicThreeDM) := by
  have normalized := PeriodicCNF.anchorNormalize_primrec.comp
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase_primrec
      (Variable := Variable))
  have encoded :=
    PeriodicPlanarOneInThreeToThreeDM.encodedProblem_primrec.comp normalized
  exact encoded.of_eq fun source =>
    (retainedFixedEightPeriodicThreeDMProblem_eq_encoded source).symm

theorem retainedFixedEightPeriodicThreeDMProblem_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedFixedEightPeriodicThreeDMProblem :
      PeriodicCNF Variable → PeriodicThreeDM) :=
  retainedFixedEightPeriodicThreeDMProblem_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes
