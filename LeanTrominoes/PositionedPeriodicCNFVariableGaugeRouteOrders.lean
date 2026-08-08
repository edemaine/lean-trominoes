import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDrawing
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeClauseMembership
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder

/-!
# Incidence-route orders under variable gauges

A variable gauge changes only literal offsets and translates every stored
route belonging to a clause by one common vector.  It therefore preserves
both cyclic-order invariants used by the ribbon construction: occurrence
order at variables and literal order at ternary clauses.
-/

namespace LeanTrominoes

namespace PeriodicThreeSATThree

/-- Gauging all literals maps the metadata-rich literal enumeration
pointwise without changing its two presentation indices. -/
theorem taggedLiterals_variableGauge
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell) :
    taggedLiterals (source.variableGauge gauge) =
      (taggedLiterals source).map fun tagged =>
        (tagged.1.variableGauge gauge, tagged.2) := by
  unfold taggedLiterals PeriodicCNF.variableGauge
  rw [List.zipIdx_map]
  simp only [List.flatMap_map, Prod.map, id_eq]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  simp [PeriodicClause.variableGauge, List.zipIdx_map,
    List.map_map, Function.comp_def]

end PeriodicThreeSATThree

namespace PeriodicOneInThreeToThreeDM

/-- Filtering the pointwise gauged tagged-literal list by atom commutes with
the gauge because literal atoms are unchanged. -/
theorem occurrencesOf_variableGauge
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell)
    (atom : Variable) :
    occurrencesOf (source.variableGauge gauge) atom =
      (occurrencesOf source atom).map fun tagged =>
        (tagged.1.variableGauge gauge, tagged.2) := by
  unfold occurrencesOf
  rw [PeriodicThreeSATThree.taggedLiterals_variableGauge]
  generalize PeriodicThreeSATThree.taggedLiterals source = tagged
  induction tagged with
  | nil => rfl
  | cons head tail induction =>
      have decisionEqual :
          decide ((head.1.variableGauge gauge).atom = atom) =
            decide (head.1.atom = atom) := by
        rfl
      simp only [List.map_cons, List.filter_cons]
      rw [decisionEqual, induction]
      by_cases same : decide (head.1.atom = atom) = true
      · simp [same]
      · simp [same]

/-- Occurrence-slot lookup commutes with a variable gauge. -/
theorem occurrenceAt_variableGauge
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell)
    (atom : Variable)
    (slot : OccurrenceSlot) :
    occurrenceAt (source.variableGauge gauge) atom slot =
      (occurrenceAt source atom slot).map fun tagged =>
        (tagged.1.variableGauge gauge, tagged.2) := by
  unfold occurrenceAt
  rw [occurrencesOf_variableGauge, List.getElem?_map]

end PeriodicOneInThreeToThreeDM

namespace PeriodicCNF

/-- A variable gauge preserves every finite occurrence-count bound. -/
theorem OccurrencesAtMost.variableGauge
    {Variable : Type*} [BEq Variable] [LawfulBEq Variable]
    {source : PeriodicCNF Variable}
    {bound : Nat}
    (bounded : source.OccurrencesAtMost bound)
    (gauge : Variable → Cell) :
    (source.variableGauge gauge).OccurrencesAtMost bound := by
  simpa only [OccurrencesAtMost, variableOccurrences_variableGauge]
    using bounded

end PeriodicCNF

namespace PeriodicOneInThreeNoUnits

/-- A variable gauge preserves the binary-or-ternary clause promise. -/
theorem ArityTwoOrThree.variableGauge
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (arity : ArityTwoOrThree source)
    (gauge : Variable → Cell) :
    ArityTwoOrThree (source.variableGauge gauge) := by
  intro gaugedClause gaugedClauseMember
  rcases List.mem_map.mp gaugedClauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  simpa [PeriodicClause.variableGauge]
    using arity sourceClause sourceClauseMember

end PeriodicOneInThreeNoUnits

namespace AxisDirection

/-- Antipodal rotation preserves clockwise cyclic order on genuine cardinal
directions.  The genuineness assumptions exclude the `invalid` fallback,
whose artificial rank is not rotational. -/
theorem InClockwiseOrder.opposite_of_opposites_genuine
    {first second third : AxisDirection}
    (clockwise : InClockwiseOrder first second third)
    (firstGenuine : first.opposite.IsGenuine)
    (secondGenuine : second.opposite.IsGenuine)
    (thirdGenuine : third.opposite.IsGenuine) :
    InClockwiseOrder first.opposite second.opposite third.opposite := by
  native_decide +revert

end AxisDirection

namespace PositionedPeriodicCNF

/-- Recover a positioned clause from any successful occurrence-slot lookup. -/
private theorem exists_positionedClause_of_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {atom : Variable}
    {slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot}
    {tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable}
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          source.erase atom slot = some tagged) :
    ∃ clause,
      (clause, tagged.2.1) ∈ source.clauses.zipIdx := by
  have taggedMember :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase atom slot tagged lookup).1
  simp only [PeriodicThreeSATThree.taggedLiterals,
    List.mem_flatMap, List.mem_map] at taggedMember
  rcases taggedMember with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteral, taggedLiteralMember, taggedEq⟩
  have clauseMember :
      (taggedClause.1, taggedClause.2) ∈
        source.erase.clauses.zipIdx :=
    taggedClauseMember
  change
    (taggedClause.1, taggedClause.2) ∈
      (source.clauses.map PositionedPeriodicClause.literals).zipIdx
    at clauseMember
  rw [List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨positionedTagged, positionedTaggedMember,
      positionedTaggedEqual⟩
  have clauseIndexEqual :
      positionedTagged.2 = taggedClause.2 :=
    congrArg Prod.snd positionedTaggedEqual
  subst tagged
  exact ⟨positionedTagged.1, by
    simpa only [← clauseIndexEqual] using positionedTaggedMember⟩

/-- Stable clause-direction ordering preserves the binary-or-ternary
clause promise. -/
theorem orderClausesByRouteDirection_arityTwoOrThree
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (orderClausesByRouteDirection source routes).erase := by
  intro orderedLiterals orderedLiteralsMember
  change orderedLiterals ∈
    (orderClausesByRouteDirection source routes).clauses.map
      PositionedPeriodicClause.literals at orderedLiteralsMember
  rcases List.mem_map.mp orderedLiteralsMember with
    ⟨orderedClause, orderedClauseMember, rfl⟩
  have indexedMember :
      orderedClause ∈
        (orderClausesByRouteDirection source routes).clauses.zipIdx.map
          Prod.fst := by
    simpa only [List.zipIdx_map_fst] using orderedClauseMember
  rcases List.mem_map.mp indexedMember with
    ⟨taggedClause, taggedClauseMember, rfl⟩
  rcases exists_sourceClause_of_orderedClause_mem
      routes taggedClauseMember with
    ⟨sourceClause, sourceClauseMember, orderedClauseEq⟩
  have sourceArity := arity sourceClause.literals
    (by
      change sourceClause.literals ∈
        source.clauses.map PositionedPeriodicClause.literals
      exact List.mem_map.mpr
        ⟨sourceClause,
          List.fst_mem_of_mem_zipIdx sourceClauseMember, rfl⟩)
  rw [orderedClauseEq]
  simpa only [orderClauseByRouteDirection_length]
    using sourceArity

/-- Translating every clause route by its canonical gauge shift preserves
the clockwise order of the last directions at each degree-three variable. -/
theorem VariableRoutesInOccurrenceOrder.variableGaugeCanonicalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (gauge : Variable → Cell)
    (ordered : source.VariableRoutesInOccurrenceOrder routes) :
    (source.variableGauge gauge).VariableRoutesInOccurrenceOrder
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes) := by
  intro atom first second third
    firstLookup secondLookup thirdLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        ((source.variableGauge gauge).erase) atom .first = some first
      at firstLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        ((source.variableGauge gauge).erase) atom .second = some second
      at secondLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        ((source.variableGauge gauge).erase) atom .third = some third
      at thirdLookup
  rw [erase_variableGauge,
    PeriodicOneInThreeToThreeDM.occurrenceAt_variableGauge]
    at firstLookup secondLookup thirdLookup
  rcases Option.map_eq_some_iff.mp firstLookup with
    ⟨sourceFirst, sourceFirstLookup, firstEq⟩
  rcases Option.map_eq_some_iff.mp secondLookup with
    ⟨sourceSecond, sourceSecondLookup, secondEq⟩
  rcases Option.map_eq_some_iff.mp thirdLookup with
    ⟨sourceThird, sourceThirdLookup, thirdEq⟩
  have clockwise :=
    ordered atom sourceFirst sourceSecond sourceThird
      sourceFirstLookup sourceSecondLookup sourceThirdLookup
  have firstClauseMember :=
    exists_positionedClause_of_occurrenceAt
      source sourceFirstLookup
  have secondClauseMember :=
    exists_positionedClause_of_occurrenceAt
      source sourceSecondLookup
  have thirdClauseMember :=
    exists_positionedClause_of_occurrenceAt
      source sourceThirdLookup
  rcases firstClauseMember with ⟨firstClause, firstClauseMember⟩
  rcases secondClauseMember with ⟨secondClause, secondClauseMember⟩
  rcases thirdClauseMember with ⟨thirdClause, thirdClauseMember⟩
  have firstIndices := congrArg (fun value => value.2) firstEq
  have secondIndices := congrArg (fun value => value.2) secondEq
  have thirdIndices := congrArg (fun value => value.2) thirdEq
  rw [← firstIndices, ← secondIndices, ← thirdIndices]
  rw [variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes firstClauseMember,
    variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes secondClauseMember,
    variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes thirdClauseMember]
  simp only [AxisDirection.polylineLastDirection_translatePolyline]
  exact clockwise

/-- A common translation of every route stored at a clause preserves its
clockwise first-direction order. -/
theorem TernaryClauseRoutesInClockwiseOrder.variableGaugeCanonicalIncidenceRoutes
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (gauge : Variable → Cell)
    (ordered : source.TernaryClauseRoutesInClockwiseOrder routes) :
    (source.variableGauge gauge).TernaryClauseRoutesInClockwiseOrder
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes) := by
  intro gaugedClause clauseIndex gaugedClauseMember gaugedArity
  rcases exists_sourceClause_of_variableGaugeClause_mem
      source gauge gaugedClauseMember with
    ⟨sourceClause, sourceClauseMember, gaugedClauseEq⟩
  have sourceArity : sourceClause.literals.length = 3 := by
    simpa [gaugedClauseEq, PeriodicClause.variableGauge]
      using gaugedArity
  have clockwise :=
    ordered sourceClause clauseIndex sourceClauseMember sourceArity
  rw [variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes sourceClauseMember,
    variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes sourceClauseMember,
    variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      source placement gauge routes sourceClauseMember]
  simp only [AxisDirection.polylineFirstDirection_translatePolyline]
  exact clockwise

end PositionedPeriodicCNF

namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM PeriodicOrthocrossing

/-- A ternary source clause fan inherits clockwise order directly from the
stored route family's literal-index order. -/
theorem sourceClauseRibbonFanData_clockwise_of_clockwiseRouteOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (ordered :
      source.TernaryClauseRoutesInClockwiseOrder
        presentation.toPlanarIncidencePresentation.routes)
    (entry : ActiveOccurrenceEntry source.erase)
    {positionedClause : PositionedPeriodicClause Variable}
    (clauseMember :
      (positionedClause,
        occurrenceClauseIndex source.erase
          entry.1.1 entry.1.2) ∈ source.clauses.zipIdx)
    (arity : positionedClause.literals.length = 3) :
    let planar := presentation.toPlanarIncidencePresentation
    let data := sourceClauseRibbonFanData planar
      (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
    AxisDirection.InClockwiseOrder
      (data.direction .top)
      (data.direction .left)
      (data.direction .right) := by
  let planar := presentation.toPlanarIncidencePresentation
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData planar clauseIndex
  dsimp only
  rcases exists_activeClauseOccurrenceEntry_of_literalIndex
      occurrences clauseMember (literalIndex := 0) (by omega) with
    ⟨topEntry, topMember, topIndex⟩
  rcases exists_activeClauseOccurrenceEntry_of_literalIndex
      occurrences clauseMember (literalIndex := 1) (by omega) with
    ⟨leftEntry, leftMember, leftIndex⟩
  rcases exists_activeClauseOccurrenceEntry_of_literalIndex
      occurrences clauseMember (literalIndex := 2) (by omega) with
    ⟨rightEntry, rightMember, rightIndex⟩
  let topData := occurrenceSpliceData planar topEntry
  let leftData := occurrenceSpliceData planar leftEntry
  let rightData := occurrenceSpliceData planar rightEntry
  have topClauseIndex :
      topData.indexed.1.clauseIndex = clauseIndex := by
    calc
      topData.indexed.1.clauseIndex =
          occurrenceClauseIndex source.erase
            topEntry.1.1 topEntry.1.2 :=
        (occurrenceClauseIndex_eq_indexedClauseIndex
          planar topEntry).symm
      _ = clauseIndex :=
        (mem_activeClauseOccurrenceEntries_iff
          source.erase clauseIndex topEntry).mp topMember
  have leftClauseIndex :
      leftData.indexed.1.clauseIndex = clauseIndex := by
    calc
      leftData.indexed.1.clauseIndex =
          occurrenceClauseIndex source.erase
            leftEntry.1.1 leftEntry.1.2 :=
        (occurrenceClauseIndex_eq_indexedClauseIndex
          planar leftEntry).symm
      _ = clauseIndex :=
        (mem_activeClauseOccurrenceEntries_iff
          source.erase clauseIndex leftEntry).mp leftMember
  have rightClauseIndex :
      rightData.indexed.1.clauseIndex = clauseIndex := by
    calc
      rightData.indexed.1.clauseIndex =
          occurrenceClauseIndex source.erase
            rightEntry.1.1 rightEntry.1.2 :=
        (occurrenceClauseIndex_eq_indexedClauseIndex
          planar rightEntry).symm
      _ = clauseIndex :=
        (mem_activeClauseOccurrenceEntries_iff
          source.erase clauseIndex rightEntry).mp rightMember
  have topLiteralIndex : topData.indexed.1.literalIndex = 0 := by
    calc
      topData.indexed.1.literalIndex =
          occurrenceLiteralIndex source.erase
            topEntry.1.1 topEntry.1.2 :=
        (occurrenceLiteralIndex_eq_indexedLiteralIndex
          planar topEntry).symm
      _ = 0 := topIndex
  have leftLiteralIndex : leftData.indexed.1.literalIndex = 1 := by
    calc
      leftData.indexed.1.literalIndex =
          occurrenceLiteralIndex source.erase
            leftEntry.1.1 leftEntry.1.2 :=
        (occurrenceLiteralIndex_eq_indexedLiteralIndex
          planar leftEntry).symm
      _ = 1 := leftIndex
  have rightLiteralIndex : rightData.indexed.1.literalIndex = 2 := by
    calc
      rightData.indexed.1.literalIndex =
          occurrenceLiteralIndex source.erase
            rightEntry.1.1 rightEntry.1.2 :=
        (occurrenceLiteralIndex_eq_indexedLiteralIndex
          planar rightEntry).symm
      _ = 2 := rightIndex
  have topDirection :
      data.direction .top =
        (AxisDirection.polylineFirstDirection
          (planar.routes clauseIndex 0)).opposite := by
    calc
      data.direction .top =
          data.direction
            (occurrenceClauseTerminalGroup source.erase topEntry) := by
        simp [occurrenceClauseTerminalGroup, topIndex,
          terminalGroupOfLiteralIndex]
      _ = occurrenceSourceClauseDirection planar topEntry :=
        ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
          planar width clauseIndex topEntry topMember
      _ = (AxisDirection.polylineFirstDirection
          (planar.routes topData.indexed.1.clauseIndex
            topData.indexed.1.literalIndex)).opposite :=
        occurrenceSourceClauseDirection_eq_storedRoute planar topEntry
      _ = _ := by rw [topClauseIndex, topLiteralIndex]
  have leftDirection :
      data.direction .left =
        (AxisDirection.polylineFirstDirection
          (planar.routes clauseIndex 1)).opposite := by
    calc
      data.direction .left =
          data.direction
            (occurrenceClauseTerminalGroup source.erase leftEntry) := by
        simp [occurrenceClauseTerminalGroup, leftIndex,
          terminalGroupOfLiteralIndex]
      _ = occurrenceSourceClauseDirection planar leftEntry :=
        ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
          planar width clauseIndex leftEntry leftMember
      _ = (AxisDirection.polylineFirstDirection
          (planar.routes leftData.indexed.1.clauseIndex
            leftData.indexed.1.literalIndex)).opposite :=
        occurrenceSourceClauseDirection_eq_storedRoute planar leftEntry
      _ = _ := by rw [leftClauseIndex, leftLiteralIndex]
  have rightDirection :
      data.direction .right =
        (AxisDirection.polylineFirstDirection
          (planar.routes clauseIndex 2)).opposite := by
    calc
      data.direction .right =
          data.direction
            (occurrenceClauseTerminalGroup source.erase rightEntry) := by
        simp [occurrenceClauseTerminalGroup, rightIndex,
          terminalGroupOfLiteralIndex]
      _ = occurrenceSourceClauseDirection planar rightEntry :=
        ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
          planar width clauseIndex rightEntry rightMember
      _ = (AxisDirection.polylineFirstDirection
          (planar.routes rightData.indexed.1.clauseIndex
            rightData.indexed.1.literalIndex)).opposite :=
        occurrenceSourceClauseDirection_eq_storedRoute planar rightEntry
      _ = _ := by rw [rightClauseIndex, rightLiteralIndex]
  have topGenuine :
      (AxisDirection.polylineFirstDirection
        (planar.routes clauseIndex 0)).opposite.IsGenuine := by
    rw [← topDirection]
    rw [show data.direction .top =
        occurrenceSourceClauseDirection planar topEntry by
      calc
        data.direction .top =
            data.direction
              (occurrenceClauseTerminalGroup source.erase topEntry) := by
          simp [occurrenceClauseTerminalGroup, topIndex,
            terminalGroupOfLiteralIndex]
        _ = occurrenceSourceClauseDirection planar topEntry :=
          ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
            planar width clauseIndex topEntry topMember]
    exact occurrenceSourceClauseDirection_isGenuine planar topEntry
  have leftGenuine :
      (AxisDirection.polylineFirstDirection
        (planar.routes clauseIndex 1)).opposite.IsGenuine := by
    rw [← leftDirection]
    rw [show data.direction .left =
        occurrenceSourceClauseDirection planar leftEntry by
      calc
        data.direction .left =
            data.direction
              (occurrenceClauseTerminalGroup source.erase leftEntry) := by
          simp [occurrenceClauseTerminalGroup, leftIndex,
            terminalGroupOfLiteralIndex]
        _ = occurrenceSourceClauseDirection planar leftEntry :=
          ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
            planar width clauseIndex leftEntry leftMember]
    exact occurrenceSourceClauseDirection_isGenuine planar leftEntry
  have rightGenuine :
      (AxisDirection.polylineFirstDirection
        (planar.routes clauseIndex 2)).opposite.IsGenuine := by
    rw [← rightDirection]
    rw [show data.direction .right =
        occurrenceSourceClauseDirection planar rightEntry by
      calc
        data.direction .right =
            data.direction
              (occurrenceClauseTerminalGroup source.erase rightEntry) := by
          simp [occurrenceClauseTerminalGroup, rightIndex,
            terminalGroupOfLiteralIndex]
        _ = occurrenceSourceClauseDirection planar rightEntry :=
          ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
            planar width clauseIndex rightEntry rightMember]
    exact occurrenceSourceClauseDirection_isGenuine planar rightEntry
  have storedClockwise :=
    ordered positionedClause clauseIndex clauseMember arity
  rw [topDirection, leftDirection, rightDirection]
  exact storedClockwise.opposite_of_opposites_genuine
    topGenuine leftGenuine rightGenuine

/-- Variable occurrence order and clockwise ternary-clause route order
together discharge every coordinated source-fan table lookup. -/
theorem sourceRibbonFansClockwiseCompatible_of_clockwiseRouteOrders
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      SourceVariableDirectionsInOccurrenceOrder
        presentation.toPlanarIncidencePresentation)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder
        presentation.toPlanarIncidencePresentation.routes) :
    SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation := by
  constructor
  · intro entry
    exact
      sourceVariableRibbonFanData_isClockwiseCompatible_of_occurrenceOrder
        presentation variableOrdered entry
  · intro entry
    let planar := presentation.toPlanarIncidencePresentation
    rcases exists_positionedClause_of_activeOccurrenceEntry planar entry with
      ⟨positionedClause, clauseMember⟩
    have erasedClauseMember :
        positionedClause.literals ∈ source.erase.clauses := by
      change positionedClause.literals ∈
        source.clauses.map PositionedPeriodicClause.literals
      exact List.mem_map.mpr
        ⟨positionedClause,
          List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩
    rcases arity positionedClause.literals erasedClauseMember with
      binary | ternary
    · apply sourceClauseRibbonFanData_isClockwiseCompatible_of_noRight
        presentation width occurrences arity entry
      exact sourceClauseRibbonFanData_noRight_of_binary
        planar entry clauseMember binary
    · apply sourceClauseRibbonFanData_isClockwiseCompatible_of_clockwise
        presentation width occurrences arity entry
      exact sourceClauseRibbonFanData_clockwise_of_clockwiseRouteOrder
        presentation width occurrences clauseOrdered entry
        clauseMember ternary

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
