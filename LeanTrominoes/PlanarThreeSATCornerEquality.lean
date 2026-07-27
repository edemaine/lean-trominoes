import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.PlanarThreeSATEqualityLensPlacement

/-!
# Equality links around one route corner

Straight carrier links use the narrow equality lens.  At a route bend, the
two endpoint variables instead occupy two distinct compass ports of one
`20 × 20` macrocell, while the equality clauses remain at `(5, 5)` and
`(8, 8)`.  This file gives all twelve ordered pairs of distinct ports a
fixed rectilinear drawing of their equality four-cycle.

At each port, the two routes use the inward axial ray and the one
perpendicular ray not used by the adjacent straight carrier lens.  The
whole table also stays on the macrocell side of every occupied port, so it
meets an incident carrier only at their common endpoint.  The route table is
deliberately finite.  Its complete endpoint, orthogonality, and
continuous-planarity certificate is checked once, then arbitrary links are
obtained by translation and injective renaming.
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
  ⟨(5, 5), (8, 8)⟩

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
      [[(5, 5), (5, 6), (1, 6)],
        [(5, 5), (11, 5), (11, 6)],
        [(8, 8), (1, 8), (1, 6)],
        [(8, 8), (8, 6), (11, 6)]]
  | .west, .south =>
      [[(5, 5), (5, 6), (1, 6)],
        [(5, 5), (5, 1), (6, 1)],
        [(8, 8), (1, 8), (1, 6)],
        [(8, 8), (8, 2), (6, 2), (6, 1)]]
  | .west, .north =>
      [[(5, 5), (5, 6), (1, 6)],
        [(5, 5), (9, 5), (9, 11), (6, 11)],
        [(8, 8), (1, 8), (1, 6)],
        [(8, 8), (8, 9), (6, 9), (6, 11)]]
  | .east, .west =>
      [[(5, 5), (5, 4), (10, 4), (10, 6), (11, 6)],
        [(5, 5), (9, 5), (9, 10), (1, 10), (1, 6)],
        [(8, 8), (4, 8), (4, 3), (11, 3), (11, 6)],
        [(8, 8), (8, 9), (2, 9), (2, 6), (1, 6)]]
  | .east, .south =>
      [[(5, 5), (5, 9), (9, 9), (9, 6), (11, 6)],
        [(5, 5), (5, 1), (6, 1)],
        [(8, 8), (8, 5), (11, 5), (11, 6)],
        [(8, 8), (6, 8), (6, 1)]]
  | .east, .north =>
      [[(5, 5), (6, 5), (6, 6), (11, 6)],
        [(5, 5), (5, 7), (9, 7), (9, 11), (6, 11)],
        [(8, 8), (4, 8), (4, 4), (11, 4), (11, 6)],
        [(8, 8), (8, 9), (6, 9), (6, 11)]]
  | .south, .west =>
      [[(5, 5), (5, 2), (6, 2), (6, 1)],
        [(5, 5), (9, 5), (9, 9), (1, 9), (1, 6)],
        [(8, 8), (8, 6), (4, 6), (4, 1), (6, 1)],
        [(8, 8), (2, 8), (2, 6), (1, 6)]]
  | .south, .east =>
      [[(5, 5), (5, 2), (6, 2), (6, 1)],
        [(5, 5), (11, 5), (11, 6)],
        [(8, 8), (4, 8), (4, 1), (6, 1)],
        [(8, 8), (8, 6), (11, 6)]]
  | .south, .north =>
      [[(5, 5), (6, 5), (6, 1)],
        [(5, 5), (5, 6), (9, 6), (9, 11), (6, 11)],
        [(8, 8), (4, 8), (4, 1), (6, 1)],
        [(8, 8), (8, 9), (6, 9), (6, 11)]]
  | .north, .west =>
      [[(5, 5), (6, 5), (6, 11)],
        [(5, 5), (5, 7), (1, 7), (1, 6)],
        [(8, 8), (8, 11), (6, 11)],
        [(8, 8), (8, 4), (2, 4), (2, 6), (1, 6)]]
  | .north, .east =>
      [[(5, 5), (6, 5), (6, 11)],
        [(5, 5), (5, 4), (11, 4), (11, 6)],
        [(8, 8), (8, 11), (6, 11)],
        [(8, 8), (8, 6), (11, 6)]]
  | .north, .south =>
      [[(5, 5), (6, 5), (6, 11)],
        [(5, 5), (5, 1), (6, 1)],
        [(8, 8), (8, 11), (6, 11)],
        [(8, 8), (8, 2), (6, 2), (6, 1)]]
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
        ⟨Cell.add origin (5, 5), Cell.add origin (8, 8)⟩ := by
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
