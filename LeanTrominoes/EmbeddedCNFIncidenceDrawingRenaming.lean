import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PlanarThreeSATInstantiation

/-!
# Injective renaming of finite incidence drawings

Local drawing templates are stated with small finite variable types, while
the reduction instantiates them with input-dependent variables.  This file
proves that an injective variable renaming preserves the complete drawing
certificate whenever the target placement realizes the old variable
positions.

Unlike geometric translation, renaming changes no route or vertex
coordinate.  Injectivity is used only to preserve the first-occurrence
deduplication of formula variables.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Rename one incidence's logical variable without changing its presentation
indices or clause geometry. -/
def EmbeddedCNFIncidence.rename {Source Target : Type*}
    (variableMap : Source → Target)
    (incidence : EmbeddedCNFIncidence Source) :
    EmbeddedCNFIncidence Target where
  clause := incidence.clause.rename variableMap
  clauseIndex := incidence.clauseIndex
  literal := (variableMap incidence.literal.1, incidence.literal.2)
  literalIndex := incidence.literalIndex

/-- Rename a finite incidence drawing into a supplied target placement.
Routes and all physical coordinates remain unchanged. -/
def EmbeddedCNFIncidenceDrawing.rename
    {Source Target : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Source)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    EmbeddedCNFIncidenceDrawing Target where
  formula := drawing.formula.map fun clause =>
    clause.rename variableMap
  variablePosition := targetPosition
  routes := drawing.routes

namespace EmbeddedCNFIncidenceDrawing

/-- Renaming maps the incidence metadata pointwise and preserves its order. -/
theorem incidences_rename
    {Source Target : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Source)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename variableMap targetPosition).incidences =
      drawing.incidences.map
        (EmbeddedCNFIncidence.rename variableMap) := by
  unfold incidences embeddedCNFIncidences
  rw [show (drawing.rename variableMap targetPosition).formula =
      drawing.formula.map fun clause =>
        clause.rename variableMap by rfl,
    List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  simp only [Prod.map, id_eq, EmbeddedClause.rename,
    EmbeddedClause.map]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rfl

@[simp]
theorem rename_incidences_length
    {Source Target : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Source)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename variableMap targetPosition).incidences.length =
      drawing.incidences.length := by
  rw [incidences_rename]
  simp

/-- Deduplication commutes with a map that is injective on the input list.
This local form avoids imposing constraints on values absent from a finite
drawing. -/
theorem dedup_map_of_injective_on
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (source : List Source)
    (injectiveOn :
      ∀ first ∈ source, ∀ second ∈ source,
        variableMap first = variableMap second →
          first = second) :
    (source.map variableMap).dedup =
      source.dedup.map variableMap := by
  induction source with
  | nil => rfl
  | cons head tail induction =>
      have tailInjective :
          ∀ first ∈ tail, ∀ second ∈ tail,
            variableMap first = variableMap second →
              first = second := by
        intro first firstMember second secondMember equal
        exact injectiveOn first (by simp [firstMember])
          second (by simp [secondMember]) equal
      by_cases headMember : head ∈ tail
      · have mappedHeadMember :
            variableMap head ∈ tail.map variableMap :=
          List.mem_map.mpr ⟨head, headMember, rfl⟩
        simp [headMember, mappedHeadMember,
          induction tailInjective]
      · have mappedHeadNotMember :
            variableMap head ∉ tail.map variableMap := by
          intro mappedHeadMember
          rcases List.mem_map.mp mappedHeadMember with
            ⟨other, otherMember, equal⟩
          have headEqual :
              head = other :=
            injectiveOn head (by simp) other
              (by simp [otherMember]) equal.symm
          exact headMember (headEqual ▸ otherMember)
        simp [headMember, mappedHeadNotMember,
          induction tailInjective]

/-- Renaming that is injective on the variables actually present maps the
distinct formula-variable list pointwise. -/
theorem variableVertices_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (drawing : EmbeddedCNFIncidenceDrawing Source)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (injectiveOn :
      ∀ first ∈ drawing.variableVertices,
        ∀ second ∈ drawing.variableVertices,
          variableMap first = variableMap second →
            first = second) :
    (drawing.rename variableMap targetPosition).variableVertices =
      drawing.variableVertices.map variableMap := by
  unfold variableVertices
  simp only [EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedClause.rename, EmbeddedClause.map,
    List.flatMap_map, List.map_map,
    Function.comp_def]
  have flattened :
      (drawing.formula.flatMap fun clause =>
        clause.literals.map fun literal =>
          variableMap literal.1) =
        (drawing.formula.flatMap fun clause =>
          clause.literals.map Prod.fst).map variableMap := by
    simp [List.map_flatMap, List.map_map,
      Function.comp_def]
  rw [flattened]
  apply dedup_map_of_injective_on
  intro first firstMember second secondMember equal
  exact injectiveOn first (by
      simpa [variableVertices] using firstMember)
    second (by
      simpa [variableVertices] using secondMember)
    equal

/-- If renamed variables retain their positions, the entire graph-vertex
position list is definitionally unchanged after simplification. -/
theorem vertexPositions_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (drawing : EmbeddedCNFIncidenceDrawing Source)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (injectiveOn :
      ∀ first ∈ drawing.variableVertices,
        ∀ second ∈ drawing.variableVertices,
          variableMap first = variableMap second →
            first = second)
    (positionsMatch :
      ∀ atom ∈ drawing.variableVertices,
        targetPosition (variableMap atom) =
          drawing.variablePosition atom) :
    (drawing.rename variableMap targetPosition).vertexPositions =
      drawing.vertexPositions := by
  rw [vertexPositions, vertexPositions,
    variableVertices_rename
      drawing variableMap targetPosition injectiveOn]
  simp only [EmbeddedCNFIncidenceDrawing.rename,
    List.map_map, Function.comp_def]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro atom atomMember
    exact positionsMatch atom atomMember
  · rfl

/-- Route lookup is unaffected by logical variable renaming. -/
@[simp]
theorem routeAt_rename_incidence
    {Source Target : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Source)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (incidence : EmbeddedCNFIncidence Source) :
    (drawing.rename variableMap targetPosition).routeAt
        (incidence.rename variableMap) =
      drawing.routeAt incidence := by
  rfl

/-- An incidence at a renamed presentation index is the pointwise rename of
the old incidence at the same index. -/
theorem incidenceAt_rename
    {Source Target : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Source)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (index :
      Fin (drawing.rename
        variableMap targetPosition).incidences.length) :
    let originalIndex : Fin drawing.incidences.length :=
      ⟨index.val, by
        exact index.isLt.trans_eq
          (rename_incidences_length
            drawing variableMap targetPosition)⟩
    (drawing.rename variableMap targetPosition).incidenceAt index =
      (drawing.incidenceAt originalIndex).rename variableMap := by
  intro originalIndex
  unfold incidenceAt
  have lookup := congrArg
    (fun incidences => incidences[index.val]?)
    (incidences_rename drawing variableMap targetPosition)
  rw [List.getElem?_eq_getElem index.isLt,
    List.getElem?_map,
    List.getElem?_eq_getElem originalIndex.isLt]
    at lookup
  exact Option.some.inj lookup

/-- Exact endpoint compatibility survives an injective logical renaming. -/
theorem routesMatch_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (positionsMatch :
      ∀ atom ∈ drawing.variableVertices,
        targetPosition (variableMap atom) =
          drawing.variablePosition atom)
    (routesMatch : drawing.RoutesMatch) :
    (drawing.rename variableMap targetPosition).RoutesMatch := by
  apply routesMatch_of_physical
  intro renamedClause clauseIndex clauseMember
    renamedLiteral literalIndex literalMember
  change
    (renamedClause, clauseIndex) ∈
      (drawing.formula.map fun clause =>
        clause.rename variableMap).zipIdx
    at clauseMember
  rw [List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have clauseEqual :
      renamedClause =
        taggedClause.1.rename variableMap :=
    (congrArg Prod.fst taggedClauseEqual).symm
  subst clauseIndex
  subst renamedClause
  change
    (renamedLiteral, literalIndex) ∈
      (taggedClause.1.literals.map fun literal =>
        (variableMap literal.1, literal.2)).zipIdx
    at literalMember
  rw [List.zipIdx_map] at literalMember
  rcases List.mem_map.mp literalMember with
    ⟨taggedLiteral, taggedLiteralMember,
      taggedLiteralEqual⟩
  have literalIndexEqual :
      taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd taggedLiteralEqual
  have literalEqual :
      renamedLiteral =
        (variableMap taggedLiteral.1.1,
          taggedLiteral.1.2) :=
    (congrArg Prod.fst taggedLiteralEqual).symm
  subst literalIndex
  subst renamedLiteral
  have base :=
    physicalRoutesMatch drawing routesMatch
      taggedClause.1 taggedClause.2 taggedClauseMember
      taggedLiteral.1 taggedLiteral.2 taggedLiteralMember
  constructor
  · exact base.1
  · change
      (drawing.routes
        taggedClause.2 taggedLiteral.2).getLast? =
        some
          (targetPosition
            (variableMap taggedLiteral.1.1))
    have atomMember :
        taggedLiteral.1.1 ∈ drawing.variableVertices := by
      unfold variableVertices
      rw [List.mem_dedup]
      apply List.mem_flatMap.mpr
      refine
        ⟨taggedClause.1,
          List.fst_mem_of_mem_zipIdx taggedClauseMember,
          ?_⟩
      exact List.mem_map.mpr
        ⟨taggedLiteral.1,
          List.fst_mem_of_mem_zipIdx taggedLiteralMember,
          rfl⟩
    rw [positionsMatch _ atomMember]
    exact base.2

/-- Axis alignment depends only on routes, so renaming preserves it. -/
theorem isOrthogonal_rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (orthogonal : drawing.IsOrthogonal) :
    (drawing.rename variableMap targetPosition).IsOrthogonal := by
  intro renamedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
  exact orthogonal originalIndex

/-- Continuous finite planarity survives injective variable renaming with
unchanged physical positions. -/
theorem isPlanar_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (injectiveOn :
      ∀ first ∈ drawing.variableVertices,
        ∀ second ∈ drawing.variableVertices,
          variableMap first = variableMap second →
            first = second)
    (positionsMatch :
      ∀ atom ∈ drawing.variableVertices,
        targetPosition (variableMap atom) =
          drawing.variablePosition atom)
    (planar : drawing.IsPlanar) :
    (drawing.rename variableMap targetPosition).IsPlanar := by
  have verticesEqual :=
    vertexPositions_rename drawing variableMap
      targetPosition injectiveOn positionsMatch
  constructor
  · intro renamedIndex
    let originalIndex : Fin drawing.incidences.length :=
      ⟨renamedIndex.val, by
        exact renamedIndex.isLt.trans_eq
          (rename_incidences_length
            drawing variableMap targetPosition)⟩
    have incidenceEqual :=
      incidenceAt_rename
        drawing variableMap targetPosition renamedIndex
    rw [incidenceEqual, routeAt_rename_incidence]
    exact planar.1 originalIndex
  constructor
  · intro renamedFirstIndex renamedSecondIndex different
    let originalFirstIndex : Fin drawing.incidences.length :=
      ⟨renamedFirstIndex.val, by
        exact renamedFirstIndex.isLt.trans_eq
          (rename_incidences_length
            drawing variableMap targetPosition)⟩
    let originalSecondIndex : Fin drawing.incidences.length :=
      ⟨renamedSecondIndex.val, by
        exact renamedSecondIndex.isLt.trans_eq
          (rename_incidences_length
            drawing variableMap targetPosition)⟩
    have originalDifferent :
        originalFirstIndex ≠ originalSecondIndex := by
      intro equal
      apply different
      have values :
          renamedFirstIndex.val =
            renamedSecondIndex.val := by
        simpa [originalFirstIndex,
          originalSecondIndex] using
          congrArg Fin.val equal
      exact Fin.ext values
    have firstEqual :=
      incidenceAt_rename
        drawing variableMap targetPosition renamedFirstIndex
    have secondEqual :=
      incidenceAt_rename
        drawing variableMap targetPosition renamedSecondIndex
    rw [firstEqual, secondEqual,
      routeAt_rename_incidence,
      routeAt_rename_incidence]
    exact planar.2.1 originalFirstIndex
      originalSecondIndex originalDifferent
  constructor
  · intro renamedVertexIndex renamedIncidenceIndex
    let originalVertexIndex :
        Fin drawing.vertexPositions.length :=
      ⟨renamedVertexIndex.val, by
        simpa [verticesEqual] using
          renamedVertexIndex.isLt⟩
    let originalIncidenceIndex :
        Fin drawing.incidences.length :=
      ⟨renamedIncidenceIndex.val, by
        exact renamedIncidenceIndex.isLt.trans_eq
          (rename_incidences_length
            drawing variableMap targetPosition)⟩
    have incidenceEqual :=
      incidenceAt_rename drawing variableMap
        targetPosition renamedIncidenceIndex
    have vertexEqual :
        (drawing.rename
          variableMap targetPosition).vertexPositions.get
            renamedVertexIndex =
          drawing.vertexPositions.get originalVertexIndex := by
      have lookup := congrArg
        (fun positions => positions[renamedVertexIndex.val]?)
        verticesEqual
      rw [List.getElem?_eq_getElem renamedVertexIndex.isLt,
        List.getElem?_eq_getElem originalVertexIndex.isLt]
        at lookup
      exact Option.some.inj lookup
    change
      ∀ renamedSegmentIndex :
          Fin (gridPolylineSegments
            ((drawing.rename
              variableMap targetPosition).routeAt
              ((drawing.rename
                variableMap targetPosition).incidenceAt
                renamedIncidenceIndex))).length,
        ¬((gridPolylineSegments
          ((drawing.rename
            variableMap targetPosition).routeAt
            ((drawing.rename
              variableMap targetPosition).incidenceAt
              renamedIncidenceIndex))).get
              renamedSegmentIndex).InteriorContains
            ((drawing.rename
              variableMap targetPosition).vertexPositions.get
                renamedVertexIndex)
    rw [incidenceEqual, routeAt_rename_incidence,
      vertexEqual]
    exact planar.2.2.1 originalVertexIndex
      originalIncidenceIndex
  · rw [verticesEqual]
    exact planar.2.2.2

/-- The complete finite drawing certificate transports through injective
logical renaming. -/
theorem isValid_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (injectiveOn :
      ∀ first ∈ drawing.variableVertices,
        ∀ second ∈ drawing.variableVertices,
          variableMap first = variableMap second →
            first = second)
    (positionsMatch :
      ∀ atom ∈ drawing.variableVertices,
        targetPosition (variableMap atom) =
          drawing.variablePosition atom)
    (valid : drawing.IsValid) :
    (drawing.rename variableMap targetPosition).IsValid :=
  ⟨routesMatch_rename variableMap targetPosition
      positionsMatch valid.1,
    isOrthogonal_rename variableMap targetPosition valid.2.1,
    isPlanar_rename variableMap targetPosition
      injectiveOn positionsMatch valid.2.2⟩

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
