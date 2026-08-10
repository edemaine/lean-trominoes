import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDM
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificate
import LeanTrominoes.PeriodicThreeDMFiniteDrawingSearch
import LeanTrominoes.PeriodicThreeSATThreeNonempty

/-!
# Continuously planar periodic 3DM data generated from Wang tiles

This module specializes the corrected retained-Figure-9 construction to the
computable Wang-to-periodic-3SAT-3 formula.  The empty tile set needs a
separate nonempty-clause source, because its direct Wang CNF contains an empty
clause.  We use two contradictory unit clauses as a fixed no-instance and
then feed both branches through the same planar construction.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicWangPlanarThreeDMReduction

abbrev Variable := PeriodicThreeSATThree.WangThreeSATThreeVariable

/-- A fixed atom used by the contradictory fallback formula. -/
def fallbackAtom : Variable :=
  (Sum.inl ⟨0, 0, 0, 0⟩, 0, 0)

/-- A nonempty-clause periodic CNF which is visibly unsatisfiable. -/
def fallbackFormula : PeriodicCNF Variable where
  clauses :=
    [[⟨fallbackAtom, (0, 0), true⟩],
      [⟨fallbackAtom, (0, 0), false⟩]]

theorem fallbackFormula_isLocal : fallbackFormula.IsLocal := by
  simp [fallbackFormula, PeriodicCNF.IsLocal, PeriodicClause.IsLocal,
    PeriodicClause.offsetDistance]

theorem fallbackFormula_widthAtMostThree :
    fallbackFormula.WidthAtMost 3 := by
  simp [fallbackFormula, PeriodicCNF.WidthAtMost,
    PeriodicClause.WidthAtMost]

theorem fallbackFormula_occurrencesAtMostThree :
    fallbackFormula.OccurrencesAtMost 3 := by
  intro atom
  calc
    (PeriodicCNF.variableOccurrences fallbackFormula).count atom ≤
        (PeriodicCNF.variableOccurrences fallbackFormula).length :=
      List.count_le_length
    _ ≤ 3 := by
      simp [fallbackFormula, PeriodicCNF.variableOccurrences]

theorem fallbackFormula_clausesNonempty :
    ∀ clause ∈ fallbackFormula.clauses, clause ≠ [] := by
  simp [fallbackFormula]

theorem fallbackFormula_not_satisfiable :
    ¬ fallbackFormula.Satisfiable := by
  rintro ⟨assignment, satisfies⟩
  have positive :=
    satisfies (0, 0) [⟨fallbackAtom, (0, 0), true⟩] (by
      simp [fallbackFormula])
  have negative :=
    satisfies (0, 0) [⟨fallbackAtom, (0, 0), false⟩] (by
      simp [fallbackFormula])
  simp [PeriodicClause.Holds, PeriodicLiteral.Holds, Cell.add] at positive negative
  simp [positive] at negative

/-- For nonempty tile sets, the standard Wang endpoint satisfies locality. -/
theorem wangFormula_isLocal (tiles : LeanWang.TileSet) :
    (PeriodicThreeSATThree.wangFormula tiles).IsLocal := by
  exact PeriodicThreeSATThree.formula_isLocal
    (PeriodicThreeCNF.formula_isLocal
      (WangPeriodicCNF.formula_isLocal tiles))

/-- For every tile set, the standard Wang endpoint has width at most three. -/
theorem wangFormula_widthAtMostThree (tiles : LeanWang.TileSet) :
    (PeriodicThreeSATThree.wangFormula tiles).WidthAtMost 3 := by
  exact PeriodicThreeSATThree.formula_widthAtMostThree
    (PeriodicThreeCNF.formula_widthAtMostThree
      (WangPeriodicCNF.formula tiles))

/-- For every tile set, the standard Wang endpoint uses each protovariable at
most three times. -/
theorem wangFormula_occurrencesAtMostThree (tiles : LeanWang.TileSet) :
    (PeriodicThreeSATThree.wangFormula tiles).OccurrencesAtMost 3 := by
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (PeriodicThreeSATThree.wangFormula tiles)
    (PeriodicThreeSATThree.formula_occurrencesAtMostThree
      (PeriodicThreeCNF.wangFormula tiles))

/-- Select the direct Wang formula except at the unique empty tile set, where
the contradictory nonempty-clause fallback is used. -/
def sourceFormula (tiles : LeanWang.TileSet) : PeriodicCNF Variable :=
  if tiles = [] then fallbackFormula
  else PeriodicThreeSATThree.wangFormula tiles

theorem wangFormula_primrec :
    Primrec (PeriodicThreeSATThree.wangFormula :
      LeanWang.TileSet → PeriodicCNF Variable) := by
  exact PeriodicThreeSATThree.formula_primrec.comp
    (PeriodicThreeCNF.formula_primrec.comp
      WangPeriodicCNF.formula_primrec)

theorem sourceFormula_primrec : Primrec sourceFormula := by
  have empty : Primrec fun tiles : LeanWang.TileSet => decide (tiles = []) :=
    (Primrec.eq.comp Primrec.id (Primrec.const [])).decide
  exact (Primrec.cond empty
    (Primrec.const fallbackFormula)
    wangFormula_primrec).of_eq fun tiles => by
      by_cases isEmpty : tiles = [] <;>
        simp [sourceFormula, isEmpty]

theorem sourceFormula_computable : Computable sourceFormula := by
  exact sourceFormula_primrec.to_comp

theorem sourceFormula_isLocal (tiles : LeanWang.TileSet) :
    (sourceFormula tiles).IsLocal := by
  by_cases empty : tiles = []
  · simp [sourceFormula, empty, fallbackFormula_isLocal]
  · simp [sourceFormula, empty, wangFormula_isLocal]

theorem sourceFormula_widthAtMostThree (tiles : LeanWang.TileSet) :
    (sourceFormula tiles).WidthAtMost 3 := by
  by_cases empty : tiles = []
  · simp [sourceFormula, empty, fallbackFormula_widthAtMostThree]
  · simp [sourceFormula, empty, wangFormula_widthAtMostThree]

theorem sourceFormula_occurrencesAtMostThree (tiles : LeanWang.TileSet) :
    (sourceFormula tiles).OccurrencesAtMost 3 := by
  by_cases empty : tiles = []
  · simpa [sourceFormula, empty] using fallbackFormula_occurrencesAtMostThree
  · simpa [sourceFormula, empty] using wangFormula_occurrencesAtMostThree tiles

/-- The same occurrence bound under the equality implementation selected by
generic constructions having only a `DecidableEq` parameter. -/
theorem sourceFormula_occurrencesAtMostThree_canonicalBEq
    (tiles : LeanWang.TileSet) :
    @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
      (by infer_instance) 3 (sourceFormula tiles) := by
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (sourceFormula tiles)
    (sourceFormula_occurrencesAtMostThree tiles)

theorem sourceFormula_clausesNonempty (tiles : LeanWang.TileSet) :
    ∀ clause ∈ (sourceFormula tiles).clauses, clause ≠ [] := by
  by_cases empty : tiles = []
  · simpa [sourceFormula, empty] using fallbackFormula_clausesNonempty
  · simpa [sourceFormula, empty] using
      PeriodicThreeSATThree.wangFormula_clausesNonempty tiles empty

theorem tilesPlane_empty_false : ¬ LeanWang.TilesPlane [] := by
  rintro ⟨tiling, _valid⟩
  simpa using (tiling (0, 0)).2

/-- The fallback changes no semantics: the selected source is satisfiable
exactly when the input Wang tiles tile the plane. -/
theorem sourceFormula_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ (sourceFormula tiles).Satisfiable := by
  by_cases empty : tiles = []
  · subst tiles
    simp only [sourceFormula, ↓reduceIte]
    exact iff_of_false tilesPlane_empty_false
      fallbackFormula_not_satisfiable
  · rw [sourceFormula, if_neg empty]
    constructor
    · intro tilesPlane
      exact ((PeriodicThreeSATThree.wangFormula_correct tiles).1
        tilesPlane).2.2.2
    · intro satisfiable
      apply (PeriodicThreeSATThree.wangFormula_correct tiles).2
      exact ⟨wangFormula_isLocal tiles,
        wangFormula_widthAtMostThree tiles,
        PeriodicThreeSATThree.formula_occurrencesAtMostThree
          (PeriodicThreeCNF.wangFormula tiles),
        satisfiable⟩

/-- The total planar periodic 3DM problem generated from a Wang tile set. -/
noncomputable def problem (tiles : LeanWang.TileSet) : PeriodicThreeDM :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
    (sourceFormula tiles)
    (sourceFormula_isLocal tiles)
    (sourceFormula_widthAtMostThree tiles)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
    (sourceFormula_clausesNonempty tiles)

/-- A concrete continuously planar drawing of the generated 3DM problem. -/
noncomputable def presentation (tiles : LeanWang.TileSet) :
    (problem tiles).ContinuousPlanarPresentation :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
    (sourceFormula tiles)
    (sourceFormula_isLocal tiles)
    (sourceFormula_widthAtMostThree tiles)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
    (sourceFormula_clausesNonempty tiles)

/-- The finite problem-and-drawing pair consumed by the data-only
normalization compiler. -/
noncomputable def input (tiles : LeanWang.TileSet) :
    PeriodicThreeDM.NormalizationCompiler.Input :=
  PeriodicThreeDM.NormalizationCompiler.inputOfPresentation
    (presentation tiles).toPlanarPresentation

@[simp]
theorem input_problem (tiles : LeanWang.TileSet) :
    (input tiles).problem = problem tiles := rfl

@[simp]
theorem input_drawing (tiles : LeanWang.TileSet) :
    (input tiles).drawing = (presentation tiles).drawing := rfl

/-- Every generated 3DM element has colored degree two or three. -/
theorem problem_degreeTwoOrThree (tiles : LeanWang.TileSet) :
    (problem tiles).DegreeTwoOrThree := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_degreeTwoOrThree
      (sourceFormula tiles)
      (sourceFormula_isLocal tiles)
      (sourceFormula_widthAtMostThree tiles)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
      (sourceFormula_clausesNonempty tiles)

/-- The generated drawing lies in the open halo used by the executable
finite planarity checker. -/
theorem presentation_endpointBounds (tiles : LeanWang.TileSet) :
    (presentation tiles).drawing.SegmentEndpointsInExpandedSquare := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_endpointBounds
      (sourceFormula tiles)
      (sourceFormula_isLocal tiles)
      (sourceFormula_widthAtMostThree tiles)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
      (sourceFormula_clausesNonempty tiles)

/-- Distinct lifted routes of the generated drawing are separated. -/
theorem presentation_separated (tiles : LeanWang.TileSet) :
    (presentation tiles).drawing.LiftedRoutesAvoidEachOther := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_separated
      (sourceFormula tiles)
      (sourceFormula_isLocal tiles)
      (sourceFormula_widthAtMostThree tiles)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
      (sourceFormula_clausesNonempty tiles)

/-- Every route stored in the generated drawing is simple. -/
theorem presentation_routesSimple (tiles : LeanWang.TileSet) :
    ∀ route ∈ (presentation tiles).drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_routesSimple
      (sourceFormula tiles)
      (sourceFormula_isLocal tiles)
      (sourceFormula_widthAtMostThree tiles)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
      (sourceFormula_clausesNonempty tiles)

/-- Listed points of distinct lifted routes meet only at genuine route
endpoints. -/
theorem presentation_endpointContacts (tiles : LeanWang.TileSet) :
    (presentation tiles).drawing.RoutePointsMeetOnlyAtEndpoints := by
  exact
    PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
      (presentation_separated tiles) (presentation_routesSimple tiles)

/-- The existing concrete drawing is a witness that the combined finite
drawing verifier always succeeds on the generated problem. -/
theorem presentation_verifies (tiles : LeanWang.TileSet) :
    PeriodicThreeDM.FiniteDrawingCertificate.verifies
      (problem tiles) (presentation tiles).drawing = true := by
  exact
    PeriodicThreeDM.FiniteDrawingCertificate.verifies_complete
      (presentation tiles).compatible
      (presentation tiles).orthogonal
      (presentation_endpointBounds tiles)
      (presentation tiles).continuouslyPlanar
      (presentation_endpointContacts tiles)

/-- The concrete construction proves that exhaustive finite-certificate
search is total on every Wang input. -/
theorem problem_hasVerifiedDrawing (tiles : LeanWang.TileSet) :
    PeriodicThreeDM.FiniteDrawingSearch.HasVerifiedDrawing (problem tiles) :=
  ⟨(presentation tiles).drawing, presentation_verifies tiles⟩

/-- A presentation reconstructed from the first finite drawing certificate
in the standard natural-number encoding.  Its definition no longer depends
on the concrete geometric construction, except through the proof that search
terminates. -/
noncomputable def searchedCertifiedPresentation (tiles : LeanWang.TileSet) :
    PeriodicThreeDM.FiniteDrawingCertificate.CertifiedPresentation
      (problem tiles) :=
  PeriodicThreeDM.FiniteDrawingSearch.searchCertifiedPresentation
    problem
    (fun tiles => (presentation tiles).problemWellFormed)
    problem_hasVerifiedDrawing
    tiles

/-- The generated continuously planar periodic 3DM problem is satisfiable
exactly when the input Wang tile set tiles the plane. -/
theorem problem_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ (problem tiles).Satisfiable := by
  exact (sourceFormula_correct tiles).trans
    (PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_satisfiable_iff
      (sourceFormula tiles)
      (sourceFormula_isLocal tiles)
      (sourceFormula_widthAtMostThree tiles)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
      (sourceFormula_clausesNonempty tiles)).symm

end PeriodicWangPlanarThreeDMReduction
end LeanTrominoes
