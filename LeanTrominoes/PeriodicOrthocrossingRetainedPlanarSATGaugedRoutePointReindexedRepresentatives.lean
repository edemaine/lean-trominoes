import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedReindexedRepresentatives
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCommonShiftRepresentatives

/-!
# Reindexing final route points through translated retained metadata

Segment-source reindexing translates the whole selected finite route.
Consequently the same construction preserves every indexed point of that
route, its route length, and its lifted physical position.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Translating a point's retained source and subtracting the same lattice
shift from its external occurrence leaves its physical position unchanged. -/
private theorem reindexedPoint_translate_sub
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (point : Cell)
    (physicalShift reindexShift : Cell) :
    Cell.add
        (Cell.add (placement.translation reindexShift) point)
        (placement.translation
          (Cell.sub physicalShift reindexShift)) =
      Cell.add point (placement.translation physicalShift) := by
  rcases point with ⟨pointX, pointY⟩
  rcases physicalShift with ⟨physicalX, physicalY⟩
  rcases reindexShift with ⟨reindexX, reindexY⟩
  apply Prod.ext <;>
    simp [PeriodicVariablePlacement.translation,
      Cell.scale, Cell.add, Cell.sub] <;>
    ring

/-- A metadata reindexing of the first-segment witness induces a
same-indexed route-point representative at the adjusted common shift. -/
def
    FinalGaugedSegmentMetadataReindexing.toRoutePointCommonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift reindexShift : Cell}
    {witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift}
    (reindexing :
      FinalGaugedSegmentMetadataReindexing
        witness.segmentWitness reindexShift) :
    FinalGaugedRoutePointCommonShiftRepresentative
      formula indexed shift
        (Cell.sub witness.segmentWitness.physicalShift
          reindexShift) := by
  let sourceIncidence :=
    metadataPhysicalIncidence
      witness.segmentWitness.routeWitness.metadata
      witness.segmentWitness.routeWitness.metadataIndex
      witness.segmentWitness.routeWitness.literal
      witness.segmentWitness.taggedLiteral.2
  let targetIncidence :=
    metadataPhysicalIncidence
      reindexing.targetMetadata reindexing.targetMetadataIndex
      reindexing.targetLiteral witness.segmentWitness.taggedLiteral.2
  let targetIncidenceIndex :=
    reindexing.targetPhysicalIncidenceIndex
  let offset :=
    carrierMacroPeriodTranslation
      (PeriodicCNF.incidenceGraph formula) reindexShift
  have targetIncidenceMember :
      (targetIncidence, targetIncidenceIndex) ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).incidences.zipIdx := by
    simpa only [targetIncidence, targetIncidenceIndex] using
      reindexing.targetPhysicalIncidenceMember
  have targetRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          targetIncidence =
        translatePolyline offset
          ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
            sourceIncidence) := by
    simpa only [targetIncidence, sourceIncidence, offset] using
      reindexing.targetRoute_eq_translate
  let targetPoint := Cell.add offset witness.physicalPoint
  have targetPointMember :
      (targetPoint, indexed.pointIndex) ∈
        ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          targetIncidence).zipIdx := by
    rw [targetRouteEq, translatePolyline, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(witness.physicalPoint, indexed.pointIndex),
        by
          simpa only [sourceIncidence] using
            witness.physicalPointMember,
        rfl⟩
  have targetRouteLengthEq :
      ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
        targetIncidence).length =
          indexed.routeLength := by
    rw [targetRouteEq]
    simpa [translatePolyline, sourceIncidence] using
      witness.physicalRouteLengthEq
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have offsetEq :
      offset = placement.translation reindexShift := by
    exact
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula reindexShift).symm
  have targetPhysicalEq :
      Cell.add targetPoint
          (placement.translation
            (Cell.sub witness.segmentWitness.physicalShift
              reindexShift)) =
        Cell.add witness.physicalPoint
          (placement.translation
            witness.segmentWitness.physicalShift) := by
    rw [show targetPoint =
        Cell.add (placement.translation reindexShift)
          witness.physicalPoint by
      simpa only [targetPoint] using
        congrArg
          (fun translate =>
            Cell.add translate witness.physicalPoint)
          offsetEq]
    exact reindexedPoint_translate_sub
      placement witness.physicalPoint
      witness.segmentWitness.physicalShift reindexShift
  refine {
    physicalIncidence := targetIncidence
    physicalIncidenceIndex := targetIncidenceIndex
    physicalIncidenceMember := targetIncidenceMember
    physicalPoint := targetPoint
    physicalPointMember := targetPointMember
    physicalRouteLengthEq := targetRouteLengthEq
    pointEq := ?_
  }
  exact witness.pointEq.trans targetPhysicalEq.symm

@[simp]
theorem
    FinalGaugedSegmentMetadataReindexing.toRoutePointCommonShiftRepresentative_physicalIncidenceIndex
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift reindexShift : Cell}
    {witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift}
    (reindexing :
      FinalGaugedSegmentMetadataReindexing
        witness.segmentWitness reindexShift) :
    (reindexing.toRoutePointCommonShiftRepresentative).physicalIncidenceIndex =
      reindexing.targetPhysicalIncidenceIndex := by
  rfl

/-- Every metadata reindexing yields a route-point representative at its
adjusted common physical shift. -/
theorem
    FinalGaugedSegmentMetadataReindexing.exists_routePointCommonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift reindexShift : Cell}
    {witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift}
    (reindexing :
      FinalGaugedSegmentMetadataReindexing
        witness.segmentWitness reindexShift) :
    Nonempty
      (FinalGaugedRoutePointCommonShiftRepresentative
        formula indexed shift
          (Cell.sub witness.segmentWitness.physicalShift
            reindexShift)) :=
  ⟨reindexing.toRoutePointCommonShiftRepresentative⟩

end PeriodicOrthocrossing
end LeanTrominoes
