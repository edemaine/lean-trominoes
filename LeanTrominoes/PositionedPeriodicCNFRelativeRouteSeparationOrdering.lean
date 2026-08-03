import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparation
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering
import LeanTrominoes.RetainedRayRasterizationTranslation

/-!
# Relative route separation under clause-direction ordering

Clause-direction ordering stably permutes each clause's literal occurrences
and translates every selected route by a whole-period anchor gauge.  This
module gives a coordinate-indexed equivalent of relative incidence
separation and uses it to transport the certificate through that permutation
and gauge change.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Relative route separation indexed directly by the two presentation
coordinates of each genuine incidence. -/
def CoordinateRelativeIncidenceRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : Prop :=
  ∀ firstClause firstClauseIndex,
    (firstClause, firstClauseIndex) ∈ source.clauses.zipIdx →
    ∀ firstLiteral firstLiteralIndex,
      (firstLiteral, firstLiteralIndex) ∈
          firstClause.literals.zipIdx →
      ∀ secondClause secondClauseIndex,
        (secondClause, secondClauseIndex) ∈ source.clauses.zipIdx →
        ∀ secondLiteral secondLiteralIndex,
          (secondLiteral, secondLiteralIndex) ∈
              secondClause.literals.zipIdx →
          ∀ relativeTranslate,
            ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
                ((secondClauseIndex, secondLiteralIndex),
                  relativeTranslate) →
              RoutesAvoidEachOther
                (routes firstClauseIndex firstLiteralIndex)
                ((routes secondClauseIndex secondLiteralIndex).map
                  (Cell.add
                    (placement.translation relativeTranslate)))

/-- Flat-indexed relative separation implies its coordinate-indexed form. -/
theorem RelativeIncidenceRoutesAvoidEachOther.coordinate
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (separated :
      RelativeIncidenceRoutesAvoidEachOther source placement routes) :
    CoordinateRelativeIncidenceRoutesAvoidEachOther
      source placement routes := by
  intro firstClause firstClauseIndex firstClauseMember
    firstLiteral firstLiteralIndex firstLiteralMember
    secondClause secondClauseIndex secondClauseMember
    secondLiteral secondLiteralIndex secondLiteralMember
    relativeTranslate coordinatesDifferent
  rcases exists_taggedIncidenceRoute_of_positioned_members
      source placement routes firstClauseMember firstLiteralMember with
    ⟨firstFlatIndex, firstMember, _⟩
  rcases exists_taggedIncidenceRoute_of_positioned_members
      source placement routes secondClauseMember secondLiteralMember with
    ⟨secondFlatIndex, secondMember, _⟩
  have occurrencesDifferent :
      (firstFlatIndex, (0, 0)) ≠
        (secondFlatIndex, relativeTranslate) := by
    intro equal
    have flatIndicesEqual : firstFlatIndex = secondFlatIndex :=
      congrArg (fun occurrence : Nat × Cell => occurrence.1) equal
    have translatesEqual : (0, 0) = relativeTranslate :=
      congrArg (fun occurrence : Nat × Cell => occurrence.2) equal
    have firstLookup := (List.mem_zipIdx_iff_getElem?).mp firstMember
    have secondLookup := (List.mem_zipIdx_iff_getElem?).mp secondMember
    rw [flatIndicesEqual, secondLookup] at firstLookup
    have incidencesEqual := Option.some.inj firstLookup.symm
    apply coordinatesDifferent
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg CNFIncidence.clauseIndex incidencesEqual
      · exact congrArg CNFIncidence.literalIndex incidencesEqual
    · exact translatesEqual
  exact
    separated
      (⟨firstClauseIndex, firstClause.literals,
        firstLiteralIndex, firstLiteral⟩, firstFlatIndex)
      firstMember
      (⟨secondClauseIndex, secondClause.literals,
        secondLiteralIndex, secondLiteral⟩, secondFlatIndex)
      secondMember relativeTranslate occurrencesDifferent

/-- Coordinate-indexed relative separation implies the original flat-indexed
interface. -/
theorem CoordinateRelativeIncidenceRoutesAvoidEachOther.relative
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (separated :
      CoordinateRelativeIncidenceRoutesAvoidEachOther
        source placement routes) :
    RelativeIncidenceRoutesAvoidEachOther source placement routes := by
  intro first firstMember second secondMember
    relativeTranslate occurrencesDifferent
  rcases incidenceMetadata_of_tagged source firstMember with
    ⟨firstClause, firstLiteral,
      firstClauseMember, firstLiteralMember, _⟩
  rcases incidenceMetadata_of_tagged source secondMember with
    ⟨secondClause, secondLiteral,
      secondClauseMember, secondLiteralMember, _⟩
  have coordinatesDifferent :
      ((first.1.clauseIndex, first.1.literalIndex), (0, 0)) ≠
        ((second.1.clauseIndex, second.1.literalIndex),
          relativeTranslate) := by
    intro equal
    have clauseIndicesEqual :
        first.1.clauseIndex = second.1.clauseIndex :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
        equal
    have literalIndicesEqual :
        first.1.literalIndex = second.1.literalIndex :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.2)
        equal
    have translatesEqual : (0, 0) = relativeTranslate :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
        equal
    have flatIndicesEqual : first.2 = second.2 := by
      by_contra flatIndicesDifferent
      rcases incidenceCoordinatesDistinct_of_flatIndicesDistinct
          source firstMember secondMember flatIndicesDifferent with
        clauseDifferent | literalDifferent
      · exact clauseDifferent clauseIndicesEqual
      · exact literalDifferent literalIndicesEqual
    apply occurrencesDifferent
    exact Prod.ext flatIndicesEqual translatesEqual
  exact separated
    firstClause first.1.clauseIndex firstClauseMember
    firstLiteral first.1.literalIndex firstLiteralMember
    secondClause second.1.clauseIndex secondClauseMember
    secondLiteral second.1.literalIndex secondLiteralMember
    relativeTranslate coordinatesDifferent

/-- A genuine ordered literal exposes the precise original tagged literal
stored at its new presentation index. -/
theorem exists_sourceLiteralTag_of_orderedLiteral_mem
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    (routes : IncidenceRoutes)
    {orderedClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (orderedClause, clauseIndex) ∈
        (orderClausesByRouteDirection source routes).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ orderedClause.literals.zipIdx) :
    ∃ sourceClause taggedLiteral,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
      taggedLiteral ∈ sourceClause.literals.zipIdx ∧
      orderedClause =
        orderClauseByRouteDirection routes clauseIndex sourceClause ∧
      (clauseLiteralOrder routes clauseIndex sourceClause)[literalIndex]? =
        some taggedLiteral ∧
      literal = taggedLiteral.1 := by
  rcases exists_sourceClause_of_orderedClause_mem
      routes clauseMember with
    ⟨sourceClause, sourceClauseMember, orderedClauseEq⟩
  have literalLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp literalMember
  rw [orderedClauseEq, orderClauseByRouteDirection,
    List.getElem?_map, Option.map_eq_some_iff] at literalLookup
  rcases literalLookup with
    ⟨taggedLiteral, taggedLookup, taggedLiteralEq⟩
  have taggedMember :
      taggedLiteral ∈ sourceClause.literals.zipIdx :=
    (clauseLiteralOrder_perm
      routes clauseIndex sourceClause).mem_iff.mp
      (List.mem_iff_getElem?.mpr ⟨literalIndex, taggedLookup⟩)
  exact ⟨sourceClause, taggedLiteral,
    sourceClauseMember, taggedMember, orderedClauseEq,
    taggedLookup, taggedLiteralEq.symm⟩

/-- Stable clause-direction ordering and its whole-period anchor gauges
preserve relative incidence-route separation. -/
theorem
    CoordinateRelativeIncidenceRoutesAvoidEachOther.orderCanonicalRoutesByClauseDirection
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (separated :
      CoordinateRelativeIncidenceRoutesAvoidEachOther
        source placement routes) :
    CoordinateRelativeIncidenceRoutesAvoidEachOther
      (orderClausesByRouteDirection source routes)
      placement
      (orderCanonicalRoutesByClauseDirection source placement routes) := by
  intro firstOrderedClause firstClauseIndex firstClauseMember
    firstLiteral firstLiteralIndex firstLiteralMember
    secondOrderedClause secondClauseIndex secondClauseMember
    secondLiteral secondLiteralIndex secondLiteralMember
    relativeTranslate orderedOccurrencesDifferent
  rcases exists_sourceLiteralTag_of_orderedLiteral_mem
      routes firstClauseMember firstLiteralMember with
    ⟨firstSourceClause, firstTaggedLiteral,
      firstSourceClauseMember, firstTaggedLiteralMember,
      firstOrderedClauseEq, firstTaggedLookup, firstLiteralEq⟩
  rcases exists_sourceLiteralTag_of_orderedLiteral_mem
      routes secondClauseMember secondLiteralMember with
    ⟨secondSourceClause, secondTaggedLiteral,
      secondSourceClauseMember, secondTaggedLiteralMember,
      secondOrderedClauseEq, secondTaggedLookup, secondLiteralEq⟩
  let firstGauge :=
    Cell.sub
      (PeriodicCNF.clauseAnchor firstSourceClause.literals)
      (PeriodicCNF.clauseAnchor firstOrderedClause.literals)
  let secondGauge :=
    Cell.sub
      (PeriodicCNF.clauseAnchor secondSourceClause.literals)
      (PeriodicCNF.clauseAnchor secondOrderedClause.literals)
  let adjustedTranslate :=
    Cell.sub (Cell.add relativeTranslate secondGauge) firstGauge
  have sourceOccurrencesDifferent :
      ((firstClauseIndex, firstTaggedLiteral.2), (0, 0)) ≠
        ((secondClauseIndex, secondTaggedLiteral.2),
          adjustedTranslate) := by
    intro equal
    have clauseIndicesEqual : firstClauseIndex = secondClauseIndex :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
        equal
    have sourceLiteralIndicesEqual :
        firstTaggedLiteral.2 = secondTaggedLiteral.2 :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.2)
        equal
    have adjustedEqual : (0, 0) = adjustedTranslate :=
      congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
        equal
    have sourceClausesEqual : firstSourceClause = secondSourceClause := by
      have firstLookup :=
        (List.mk_mem_zipIdx_iff_getElem?).mp firstSourceClauseMember
      have secondLookup :=
        (List.mk_mem_zipIdx_iff_getElem?).mp secondSourceClauseMember
      rw [clauseIndicesEqual, secondLookup] at firstLookup
      exact Option.some.inj firstLookup.symm
    have taggedLiteralsEqual :
        firstTaggedLiteral = secondTaggedLiteral := by
      apply Prod.ext
      · have firstLookup :=
          (List.mem_zipIdx_iff_getElem?).mp firstTaggedLiteralMember
        have secondLookup :=
          (List.mem_zipIdx_iff_getElem?).mp secondTaggedLiteralMember
        rw [sourceClausesEqual, sourceLiteralIndicesEqual,
          secondLookup] at firstLookup
        exact Option.some.inj firstLookup.symm
      · exact sourceLiteralIndicesEqual
    have orderedClausesEqual :
        firstOrderedClause = secondOrderedClause := by
      rw [firstOrderedClauseEq, secondOrderedClauseEq,
        sourceClausesEqual, clauseIndicesEqual]
    have orderedLiteralIndicesEqual :
        firstLiteralIndex = secondLiteralIndex := by
      have orderNodup :
          (clauseLiteralOrder routes firstClauseIndex
            firstSourceClause).Nodup :=
        (clauseLiteralOrder_perm
          routes firstClauseIndex firstSourceClause).nodup_iff.mpr
          ((List.nodup_zipIdx_map_snd
            firstSourceClause.literals).of_map Prod.snd)
      rcases List.getElem?_eq_some_iff.mp firstTaggedLookup with
        ⟨firstLt, firstAt⟩
      have secondLookupSame :
          (clauseLiteralOrder routes firstClauseIndex
              firstSourceClause)[secondLiteralIndex]? =
            some firstTaggedLiteral := by
        simpa [sourceClausesEqual, clauseIndicesEqual,
          taggedLiteralsEqual] using secondTaggedLookup
      rcases List.getElem?_eq_some_iff.mp secondLookupSame with
        ⟨secondLt, secondAt⟩
      exact
        ((orderNodup.getElem_inj_iff
          (hi := firstLt) (hj := secondLt)).mp
          (firstAt.trans secondAt.symm))
    have gaugesEqual : firstGauge = secondGauge := by
      simp [firstGauge, secondGauge, sourceClausesEqual,
        orderedClausesEqual]
    have relativeEqual : relativeTranslate = (0, 0) := by
      rcases relativeTranslate with ⟨relativeX, relativeY⟩
      rcases firstGauge with ⟨firstGaugeX, firstGaugeY⟩
      rcases secondGauge with ⟨secondGaugeX, secondGaugeY⟩
      simp [adjustedTranslate, Cell.add, Cell.sub] at adjustedEqual gaugesEqual
      apply Prod.ext <;> omega
    apply orderedOccurrencesDifferent
    apply Prod.ext
    · exact Prod.ext clauseIndicesEqual orderedLiteralIndicesEqual
    · exact relativeEqual.symm
  have sourceAvoids := separated
    firstSourceClause firstClauseIndex firstSourceClauseMember
    firstTaggedLiteral.1 firstTaggedLiteral.2 firstTaggedLiteralMember
    secondSourceClause secondClauseIndex secondSourceClauseMember
    secondTaggedLiteral.1 secondTaggedLiteral.2 secondTaggedLiteralMember
    adjustedTranslate sourceOccurrencesDifferent
  have firstSourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp firstSourceClauseMember
  have secondSourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp secondSourceClauseMember
  have firstRouteEq :
      LeanTrominoes.PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
          source placement routes
          firstClauseIndex firstLiteralIndex =
        PeriodicOrthocrossing.translatePolyline
          (placement.translation firstGauge)
          (routes firstClauseIndex firstTaggedLiteral.2) := by
    simp [LeanTrominoes.PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection,
      orderRoutesByClauseDirection, firstSourceClauseLookup,
      firstTaggedLookup, firstGauge, firstOrderedClauseEq]
  have secondRouteEq :
      LeanTrominoes.PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
          source placement routes
          secondClauseIndex secondLiteralIndex =
        PeriodicOrthocrossing.translatePolyline
          (placement.translation secondGauge)
          (routes secondClauseIndex secondTaggedLiteral.2) := by
    simp [LeanTrominoes.PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection,
      orderRoutesByClauseDirection, secondSourceClauseLookup,
      secondTaggedLookup, secondGauge, secondOrderedClauseEq]
  rw [firstRouteEq, secondRouteEq]
  have translatedAvoids :=
    sourceAvoids.translate (placement.translation firstGauge)
  have secondTranslationEq :
      PeriodicOrthocrossing.translatePolyline
          (placement.translation firstGauge)
          ((routes secondClauseIndex secondTaggedLiteral.2).map
            (Cell.add (placement.translation adjustedTranslate))) =
        (PeriodicOrthocrossing.translatePolyline
          (placement.translation secondGauge)
          (routes secondClauseIndex secondTaggedLiteral.2)).map
            (Cell.add (placement.translation relativeTranslate)) := by
    unfold PeriodicOrthocrossing.translatePolyline
    simp only [List.map_map]
    apply List.map_congr_left
    intro point _pointMember
    rcases point with ⟨pointX, pointY⟩
    rcases firstGauge with ⟨firstGaugeX, firstGaugeY⟩
    rcases secondGauge with ⟨secondGaugeX, secondGaugeY⟩
    rcases relativeTranslate with ⟨relativeX, relativeY⟩
    simp [adjustedTranslate, PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale]
    constructor <;> ring
  rw [secondTranslationEq] at translatedAvoids
  exact translatedAvoids

/-- Flat-indexed relative separation survives stable clause-direction
ordering and canonical anchor-gauge translation. -/
theorem
    RelativeIncidenceRoutesAvoidEachOther.orderCanonicalRoutesByClauseDirection
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (separated :
      RelativeIncidenceRoutesAvoidEachOther source placement routes) :
    RelativeIncidenceRoutesAvoidEachOther
      (orderClausesByRouteDirection source routes)
      placement
      (orderCanonicalRoutesByClauseDirection source placement routes) :=
  separated.coordinate.orderCanonicalRoutesByClauseDirection.relative

end PositionedPeriodicCNF
end LeanTrominoes
