import LeanTrominoes.EmbeddedCNFIncidenceDrawingAxisPlacement
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.PlanarThreeSATEqualityLens

/-!
# Placing and renaming the equality lens

The canonical lens uses `Bool` endpoints and points east from the origin.
This file turns it into a reusable drawing for any two distinct logical
variables, arbitrary origin, and any directed grid axis.  Its formula,
endpoint positions, and complete geometric certificate are exposed in the
form needed by carrier-link assembly.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Rename the two Boolean template endpoints to an arbitrary ordered pair. -/
def equalityLensVariableMap
    {Variable : Type*} (first second : Variable) : Bool → Variable
  | false => first
  | true => second

/-- Distinct target endpoints make the two-role variable map injective. -/
theorem equalityLensVariableMap_injective
    {Variable : Type*}
    {first second : Variable}
    (different : first ≠ second) :
    Function.Injective (equalityLensVariableMap first second) := by
  intro firstRole secondRole equal
  cases firstRole <;> cases secondRole <;>
    simp_all [equalityLensVariableMap]

/-- First rotate and translate the Boolean equality-lens template. -/
def axisEqualityLensDrawing
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    EmbeddedCNFIncidenceDrawing Bool :=
  (horizontalEqualityLensDrawing span).placeOnAxis
    origin direction

/-- Rename a placed equality lens to an arbitrary pair of logical
variables.  The canonical image-position construction supplies irrelevant
defaults away from those two variables. -/
def placedEqualityLensDrawing
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    EmbeddedCNFIncidenceDrawing Variable :=
  (axisEqualityLensDrawing origin direction span).renameToImage
    (equalityLensVariableMap first second)

/-- The positioned lens contains exactly the requested equality clauses at
the oriented images of canonical coordinates `3` and `6`. -/
theorem placedEqualityLensDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (placedEqualityLensDrawing
      first second origin direction span).formula =
      equalityInstance first second
        ⟨direction.placePoint origin (3, 0),
          direction.placePoint origin (6, 0)⟩ := by
  simp [placedEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    axisEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.placeOnAxis,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedClause.translate,
    EmbeddedCNFIncidenceDrawing.orient,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    EmbeddedClause.mapPosition,
    horizontalEqualityLensDrawing,
    horizontalEqualityLensPositions,
    EmbeddedClause.rename,
    EmbeddedClause.map,
    equalityInstance,
    equalityLensVariableMap,
    AxisDirection.placePoint]

/-- The first renamed endpoint is placed at the chosen origin. -/
theorem placedEqualityLensDrawing_firstPosition
    {Variable : Type*} [DecidableEq Variable]
    {first second : Variable}
    (different : first ≠ second)
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (placedEqualityLensDrawing
      first second origin direction span).variablePosition first =
      origin := by
  let base := axisEqualityLensDrawing origin direction span
  have injective :
      Function.Injective (equalityLensVariableMap first second) :=
    equalityLensVariableMap_injective different
  have falseMember : false ∈ base.variableVertices := by
    dsimp [base, axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.orient]
    rw [EmbeddedCNFIncidenceDrawing.variableVertices_translate,
      EmbeddedCNFIncidenceDrawing.variableVertices_mapPoints]
    simp [
      horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      EmbeddedCNFIncidenceDrawing.variableVertices,
      equalityInstance]
  change
    EmbeddedCNFIncidenceDrawing.imageVariablePosition
        base (equalityLensVariableMap first second)
          (equalityLensVariableMap first second false) =
      origin
  rw [EmbeddedCNFIncidenceDrawing.imageVariablePosition_map
      base (equalityLensVariableMap first second)
      (fun firstRole _ secondRole _ equal =>
        injective equal) false falseMember]
  cases direction <;>
    simp [base, axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.translate,
      EmbeddedCNFIncidenceDrawing.orient,
      EmbeddedCNFIncidenceDrawing.mapPoints,
      horizontalEqualityLensDrawing,
      horizontalEqualityLensVariablePosition,
      AxisDirection.orientPoint, Cell.add]

/-- The second renamed endpoint is the oriented point at the requested
span. -/
theorem placedEqualityLensDrawing_secondPosition
    {Variable : Type*} [DecidableEq Variable]
    {first second : Variable}
    (different : first ≠ second)
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (placedEqualityLensDrawing
      first second origin direction span).variablePosition second =
      direction.placePoint origin (span, 0) := by
  let base := axisEqualityLensDrawing origin direction span
  have injective :
      Function.Injective (equalityLensVariableMap first second) :=
    equalityLensVariableMap_injective different
  have trueMember : true ∈ base.variableVertices := by
    dsimp [base, axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.orient]
    rw [EmbeddedCNFIncidenceDrawing.variableVertices_translate,
      EmbeddedCNFIncidenceDrawing.variableVertices_mapPoints]
    simp [
      horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      EmbeddedCNFIncidenceDrawing.variableVertices,
      equalityInstance]
  change
    EmbeddedCNFIncidenceDrawing.imageVariablePosition
        base (equalityLensVariableMap first second)
          (equalityLensVariableMap first second true) =
      direction.placePoint origin (span, 0)
  rw [EmbeddedCNFIncidenceDrawing.imageVariablePosition_map
      base (equalityLensVariableMap first second)
      (fun firstRole _ secondRole _ equal =>
        injective equal) true trueMember]
  rfl

/-- Every sufficiently long placed lens retains exact endpoints,
orthogonality, and continuous planarity. -/
theorem placedEqualityLensDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    {first second : Variable}
    (different : first ≠ second)
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    (placedEqualityLensDrawing
      first second origin direction span).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.renameToImage_isValid
  · intro firstRole _ secondRole _ equal
    exact equalityLensVariableMap_injective different equal
  · exact
      EmbeddedCNFIncidenceDrawing.isValid_placeOnAxis
        (horizontalEqualityLensDrawing_isValid span spanLarge)
        origin direction

end PlanarThreeSAT
end LeanTrominoes
