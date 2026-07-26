import LeanTrominoes.PeriodicOneInThreeAnchorNormalization
import LeanTrominoes.PeriodicPlanarThreeDMIncidenceRouting
import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds

/-!
# Normalized input to the planar exact-one-to-3DM reduction

This module packages the exact source and target objects used by the
geometric 3DM assembly.  The positioned exact-one source is first put in the
zero-anchor gauge.  Its unchanged planar incidence presentation then routes
from each variable prototype to the clause translate named by the typed 3DM
reference.

The corresponding natural-number `PeriodicThreeDM` problem is already
well-formed, has colored degree two or three, and is satisfiable exactly when
the unnormalized positioned source is exact-one satisfiable.  Thus the
remaining construction is purely geometric: it must replace the vertices
and the three routed strands without changing this fixed target problem.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Positioned exact-one source in the zero-clause-anchor gauge. -/
def normalizedPositionedSource
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF Variable :=
  source.anchorNormalize placement

/-- Erased normalized source consumed by the typed 3DM assembly. -/
def normalizedSource
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    PeriodicCNF Variable :=
  (normalizedPositionedSource source placement).erase

/-- Natural-number planar-3DM target associated with the normalized source. -/
def normalizedProblem
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    PeriodicThreeDM :=
  encodedProblem (normalizedSource source placement)

@[simp]
theorem normalizedSource_eq
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    normalizedSource source placement =
      source.erase.anchorNormalize := by
  simp [normalizedSource, normalizedPositionedSource]

/-- The normalized source retains the occurrence-three promise required by
the variable cycles. -/
theorem normalizedSource_occurrencesAtMost
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    {bound : Nat}
    (occurrences : source.erase.OccurrencesAtMost bound) :
    (normalizedSource source placement).OccurrencesAtMost bound := by
  rw [normalizedSource_eq]
  exact source.erase.anchorNormalize_occurrencesAtMost
    bound occurrences

/-- The normalized source retains the two-or-three-literal clause promise. -/
theorem normalizedSource_arityTwoOrThree
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (normalizedSource source placement) := by
  rw [normalizedSource_eq]
  exact source.erase.anchorNormalize_arityTwoOrThree arity

/-- Every reference in the normalized natural-number target names a declared
colored element. -/
theorem normalizedProblem_isWellFormed
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    (normalizedProblem source placement).IsWellFormed :=
  encodedProblem_isWellFormed (normalizedSource source placement)

/-- Every colored element of the normalized target has degree two or three. -/
theorem normalizedProblem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    (normalizedProblem source placement).DegreeTwoOrThree := by
  apply encodedProblem_degreeTwoOrThree
  apply problem_degreeTwoOrThree
  · exact normalizedSource_occurrencesAtMost
      source placement occurrences
  · exact normalizedSource_arityTwoOrThree
      source placement arity

/-- The normalized natural-number target has a perfect matching exactly when
the original positioned source has an exact-one satisfying assignment. -/
theorem normalizedProblem_satisfiable_iff_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    (normalizedProblem source placement).Satisfiable ↔
      PeriodicOneInThree.Satisfiable source.erase := by
  exact
    (encodedProblem_satisfiable_iff_source
      (normalizedSource source placement)
      (normalizedSource_occurrencesAtMost
        source placement occurrences)
      (normalizedSource_arityTwoOrThree
        source placement arity)).trans
      (source.anchorNormalize_oneInThree_satisfiable_iff placement)

/-- The abstract incidence-graph orientation of the normalized target has
the same exact-one semantics. -/
theorem normalizedProblem_graphHasOrientation_iff_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    (normalizedProblem source placement).GraphHasOrientation ↔
      PeriodicOneInThree.Satisfiable source.erase := by
  exact
    (PeriodicThreeDM.satisfiable_iff_graphHasOrientation
      (normalizedProblem source placement)).symm.trans
      (normalizedProblem_satisfiable_iff_source
        source placement occurrences arity)

/-- The normalized incidence presentation used to splice the three routed
terminal strands is literally the transported source presentation. -/
def normalizedIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.PlanarIncidencePresentation placement) :
    PositionedPeriodicCNF.PlanarIncidencePresentation
      (normalizedPositionedSource source placement) placement :=
  presentation.anchorNormalize

/-- The continuously planar splice presentation likewise transports
unchanged to the normalized source. -/
def normalizedContinuousIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement) :
    PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
      (normalizedPositionedSource source placement) placement :=
  presentation.anchorNormalize

/-- The continuously planar, rebased-route-bounded presentation transports
unchanged to the normalized source as well. -/
def normalizedHaloBoundedIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedContinuousPlanarIncidencePresentation placement) :
    PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation
      (normalizedPositionedSource source placement) placement :=
  presentation.anchorNormalize

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
