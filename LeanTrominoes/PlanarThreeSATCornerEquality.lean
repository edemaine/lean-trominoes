import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.PlanarThreeSATEqualityLensPlacement

/-!
# Equality links around one route corner

Straight carrier links use the narrow equality lens.  At a route bend, the
two endpoint variables instead occupy two distinct compass ports of one
`20 × 20` macrocell, while the equality clauses remain at `(8, 8)` and
`(12, 12)`.  This file gives all twelve ordered pairs of distinct ports a
fixed rectilinear drawing of their equality four-cycle.

The route table is deliberately finite.  Its complete endpoint,
orthogonality, and continuous-planarity certificate is checked once, then
arbitrary links are obtained by translation and injective renaming.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- The four directional terminal ports used inside a route-bend
macrocell. -/
inductive CornerPort
  | west
  | east
  | south
  | north
  deriving DecidableEq, Repr

/-- Local macrocell position of a directional route-bend port. -/
def CornerPort.position : CornerPort → Cell
  | .west => (1, 6)
  | .east => (11, 6)
  | .south => (6, 1)
  | .north => (6, 11)

/-- The two fixed implication-clause positions around every route bend. -/
def cornerEqualityPositions : EqualityPositions :=
  ⟨(8, 8), (12, 12)⟩

/-- Boolean endpoints placed at an ordered pair of compass ports. -/
def cornerEqualityVariablePosition
    (first second : CornerPort) : Bool → Cell
  | false => first.position
  | true => second.position

/-- Four incidence routes, in clause-major order, for an ordered pair of
distinct compass ports.  Equal-port cases are irrelevant and totalized by
the empty list. -/
def cornerEqualityRouteTable :
    CornerPort → CornerPort → List (List Cell)
  | .west, .east =>
      [[(8, 8), (1, 8), (1, 6)],
        [(8, 8), (11, 8), (11, 6)],
        [(12, 12), (0, 12), (0, 6), (1, 6)],
        [(12, 12), (12, 6), (11, 6)]]
  | .west, .south =>
      [[(8, 8), (1, 8), (1, 6)],
        [(8, 8), (8, 1), (6, 1)],
        [(12, 12), (0, 12), (0, 6), (1, 6)],
        [(12, 12), (12, 0), (6, 0), (6, 1)]]
  | .west, .north =>
      [[(8, 8), (1, 8), (1, 6)],
        [(8, 8), (8, 11), (6, 11)],
        [(12, 12), (12, 6), (1, 6)],
        [(12, 12), (6, 12), (6, 11)]]
  | .east, .west =>
      [[(8, 8), (11, 8), (11, 6)],
        [(8, 8), (1, 8), (1, 6)],
        [(12, 12), (12, 6), (11, 6)],
        [(12, 12), (0, 12), (0, 6), (1, 6)]]
  | .east, .south =>
      [[(8, 8), (11, 8), (11, 6)],
        [(8, 8), (6, 8), (6, 1)],
        [(12, 12), (12, 6), (11, 6)],
        [(12, 12), (0, 12), (0, 1), (6, 1)]]
  | .east, .north =>
      [[(8, 8), (11, 8), (11, 6)],
        [(8, 8), (6, 8), (6, 11)],
        [(12, 12), (12, 6), (11, 6)],
        [(12, 12), (6, 12), (6, 11)]]
  | .south, .west =>
      [[(8, 8), (6, 8), (6, 1)],
        [(8, 8), (8, 0), (1, 0), (1, 6)],
        [(12, 12), (2, 12), (2, 1), (6, 1)],
        [(12, 12), (12, 13), (1, 13), (1, 6)]]
  | .south, .east =>
      [[(8, 8), (6, 8), (6, 1)],
        [(8, 8), (11, 8), (11, 6)],
        [(12, 12), (0, 12), (0, 1), (6, 1)],
        [(12, 12), (12, 6), (11, 6)]]
  | .south, .north =>
      [[(8, 8), (6, 8), (6, 1)],
        [(8, 8), (8, 11), (6, 11)],
        [(12, 12), (12, 1), (6, 1)],
        [(12, 12), (6, 12), (6, 11)]]
  | .north, .west =>
      [[(8, 8), (6, 8), (6, 11)],
        [(8, 8), (8, 6), (1, 6)],
        [(12, 12), (6, 12), (6, 11)],
        [(12, 12), (12, 0), (1, 0), (1, 6)]]
  | .north, .east =>
      [[(8, 8), (6, 8), (6, 11)],
        [(8, 8), (11, 8), (11, 6)],
        [(12, 12), (6, 12), (6, 11)],
        [(12, 12), (12, 6), (11, 6)]]
  | .north, .south =>
      [[(8, 8), (6, 8), (6, 11)],
        [(8, 8), (8, 1), (6, 1)],
        [(12, 12), (6, 12), (6, 11)],
        [(12, 12), (12, 0), (6, 0), (6, 1)]]
  | _, _ => []

/-- Total presentation-indexed lookup into the four-route table. -/
def cornerEqualityRoutes
    (first second : CornerPort) (clauseIndex literalIndex : Nat) :
    List Cell :=
  (cornerEqualityRouteTable first second).getD
    (2 * clauseIndex + literalIndex) []

/-- The fixed equality formula at one ordered pair of macrocell ports. -/
def cornerEqualityDrawing
    (first second : CornerPort) :
    EmbeddedCNFIncidenceDrawing Bool where
  formula :=
    equalityInstance false true cornerEqualityPositions
  variablePosition :=
    cornerEqualityVariablePosition first second
  routes := cornerEqualityRoutes first second

/-- Every ordered pair of distinct compass ports has a complete fixed
incidence-drawing certificate. -/
theorem cornerEqualityDrawing_isValid
    (first second : CornerPort) (different : first ≠ second) :
    (cornerEqualityDrawing first second).IsValid := by
  cases first <;> cases second <;>
    simp_all <;> native_decide

/-- Translate the fixed corner drawing and rename its Boolean endpoints to
an arbitrary distinct pair of logical variables. -/
def placedCornerEqualityDrawing
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable) (origin : Cell)
    (firstPort secondPort : CornerPort) :
    EmbeddedCNFIncidenceDrawing Variable :=
  EmbeddedCNFIncidenceDrawing.renameToImage
    ((cornerEqualityDrawing firstPort secondPort).translate origin)
    (equalityLensVariableMap first second)

/-- A placed corner drawing contains exactly the requested equality
instance at the translated fixed clause positions. -/
theorem placedCornerEqualityDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable) (origin : Cell)
    (firstPort secondPort : CornerPort) :
    (placedCornerEqualityDrawing
      first second origin firstPort secondPort).formula =
      equalityInstance first second
        ⟨Cell.add origin (8, 8), Cell.add origin (12, 12)⟩ := by
  simp [placedCornerEqualityDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedClause.translate,
    cornerEqualityDrawing, cornerEqualityPositions,
    EmbeddedClause.rename, EmbeddedClause.map,
    equalityInstance, equalityLensVariableMap]

/-- The first renamed endpoint occupies its translated compass port. -/
theorem placedCornerEqualityDrawing_firstPosition
    {Variable : Type*} [DecidableEq Variable]
    {first second : Variable}
    (different : first ≠ second)
    (origin : Cell) (firstPort secondPort : CornerPort) :
    (placedCornerEqualityDrawing
      first second origin firstPort secondPort).variablePosition first =
      Cell.add origin firstPort.position := by
  let base :=
    (cornerEqualityDrawing firstPort secondPort).translate origin
  have injective :
      Function.Injective (equalityLensVariableMap first second) :=
    equalityLensVariableMap_injective different
  have falseMember : false ∈ base.variableVertices := by
    dsimp [base]
    rw [EmbeddedCNFIncidenceDrawing.variableVertices_translate]
    simp [cornerEqualityDrawing, cornerEqualityPositions,
      EmbeddedCNFIncidenceDrawing.variableVertices,
      equalityInstance]
  change
    EmbeddedCNFIncidenceDrawing.imageVariablePosition
        base (equalityLensVariableMap first second)
          (equalityLensVariableMap first second false) =
      Cell.add origin firstPort.position
  rw [EmbeddedCNFIncidenceDrawing.imageVariablePosition_map
      base (equalityLensVariableMap first second)
      (fun firstRole _ secondRole _ equal =>
        injective equal) false falseMember]
  rfl

/-- The second renamed endpoint occupies its translated compass port. -/
theorem placedCornerEqualityDrawing_secondPosition
    {Variable : Type*} [DecidableEq Variable]
    {first second : Variable}
    (different : first ≠ second)
    (origin : Cell) (firstPort secondPort : CornerPort) :
    (placedCornerEqualityDrawing
      first second origin firstPort secondPort).variablePosition second =
      Cell.add origin secondPort.position := by
  let base :=
    (cornerEqualityDrawing firstPort secondPort).translate origin
  have injective :
      Function.Injective (equalityLensVariableMap first second) :=
    equalityLensVariableMap_injective different
  have trueMember : true ∈ base.variableVertices := by
    dsimp [base]
    rw [EmbeddedCNFIncidenceDrawing.variableVertices_translate]
    simp [cornerEqualityDrawing, cornerEqualityPositions,
      EmbeddedCNFIncidenceDrawing.variableVertices,
      equalityInstance]
  change
    EmbeddedCNFIncidenceDrawing.imageVariablePosition
        base (equalityLensVariableMap first second)
          (equalityLensVariableMap first second true) =
      Cell.add origin secondPort.position
  rw [EmbeddedCNFIncidenceDrawing.imageVariablePosition_map
      base (equalityLensVariableMap first second)
      (fun firstRole _ secondRole _ equal =>
        injective equal) true trueMember]
  rfl

/-- Translation and injective endpoint renaming preserve the complete fixed
corner certificate. -/
theorem placedCornerEqualityDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    {first second : Variable}
    (different : first ≠ second)
    (origin : Cell) {firstPort secondPort : CornerPort}
    (portsDifferent : firstPort ≠ secondPort) :
    (placedCornerEqualityDrawing
      first second origin firstPort secondPort).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.renameToImage_isValid
  · intro firstRole _ secondRole _ equal
    exact equalityLensVariableMap_injective different equal
  · exact
      EmbeddedCNFIncidenceDrawing.isValid_translate
        (cornerEqualityDrawing_isValid
          firstPort secondPort portsDifferent) origin

end PlanarThreeSAT
end LeanTrominoes
