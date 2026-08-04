import LeanTrominoes.PeriodicOneInThreeToThreeDMOccurrences
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-!
# Variable occurrence order through clause-direction sorting

Sorting literals inside a clause changes their literal indices but not the
order in which any fixed atom occurs across clauses.  When atoms are distinct
inside every clause, the correspondingly reindexed canonical routes therefore
preserve variable-side occurrence order.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

variable {Variable : Type*} [DecidableEq Variable]

/-- The clause indices at which one atom occurs, retaining repetitions. -/
private def occurrenceClauseIndices
    (source : PositionedPeriodicCNF Variable) (atom : Variable) : List Nat :=
  (PeriodicOneInThreeToThreeDM.occurrencesOf source.erase atom).map
    fun tagged => tagged.2.1

private theorem filteredTaggedClause_clauseIndices
    (clause : PeriodicClause Variable) (clauseIndex start : Nat)
    (atom : Variable) :
    ((((clause.zipIdx start).map fun taggedLiteral =>
          (taggedLiteral.1, clauseIndex, taggedLiteral.2)).filter
        fun tagged => tagged.1.atom = atom).map
      fun tagged => tagged.2.1) =
      List.replicate
        ((clause.map PeriodicLiteral.atom).count atom) clauseIndex := by
  induction clause generalizing start with
  | nil => simp
  | cons literal rest induction =>
      by_cases same : literal.atom = atom
      · simp [same, induction, List.replicate_succ]
      · simp [same, induction]

private theorem occurrenceClauseIndices_eq_clauses
    (clauses : List (PositionedPeriodicClause Variable))
    (start : Nat) (atom : Variable) :
    (((((clauses.map PositionedPeriodicClause.literals).zipIdx start).flatMap
        fun taggedClause =>
          taggedClause.1.zipIdx.map fun taggedLiteral =>
            (taggedLiteral.1, taggedClause.2, taggedLiteral.2)).filter
      fun tagged => tagged.1.atom = atom).map
      fun tagged => tagged.2.1) =
      (clauses.zipIdx start).flatMap (fun taggedClause =>
        List.replicate
          ((taggedClause.1.literals.map PeriodicLiteral.atom).count atom)
          taggedClause.2) := by
  induction clauses generalizing start with
  | nil => simp
  | cons clause rest induction =>
      simp only [List.map_cons, List.zipIdx_cons,
        List.flatMap_cons, List.filter_append, List.map_append]
      rw [filteredTaggedClause_clauseIndices
        clause.literals start 0 atom]
      exact congrArg₂ (· ++ ·) rfl (induction (start + 1))

private theorem occurrenceClauseIndices_eq
    (source : PositionedPeriodicCNF Variable) (atom : Variable) :
    occurrenceClauseIndices source atom =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        List.replicate
          ((taggedClause.1.literals.map PeriodicLiteral.atom).count atom)
          taggedClause.2 := by
  unfold occurrenceClauseIndices PeriodicOneInThreeToThreeDM.occurrencesOf
    PeriodicThreeSATThree.taggedLiterals PositionedPeriodicCNF.erase
  exact occurrenceClauseIndices_eq_clauses source.clauses 0 atom

private theorem orderedOccurrenceCounts
    (routes : IncidenceRoutes) (atom : Variable)
    (clauses : List (PositionedPeriodicClause Variable))
    (start : Nat) :
    ((((clauses.zipIdx start).map fun taggedClause =>
          orderClauseByRouteDirection
            routes taggedClause.2 taggedClause.1).zipIdx start).flatMap
      fun taggedClause =>
        List.replicate
          ((taggedClause.1.literals.map PeriodicLiteral.atom).count atom)
          taggedClause.2) =
      (clauses.zipIdx start).flatMap fun taggedClause =>
        List.replicate
          ((taggedClause.1.literals.map PeriodicLiteral.atom).count atom)
          taggedClause.2 := by
  induction clauses generalizing start with
  | nil => simp
  | cons clause rest induction =>
      simp only [List.zipIdx_cons, List.map_cons, List.flatMap_cons]
      have countEq :=
        ((orderClauseByRouteDirection_literals_perm
          routes start clause).map PeriodicLiteral.atom).count atom
      rw [show
        (orderClauseByRouteDirection routes start clause).literals.map
            PeriodicLiteral.atom =
          ((orderClauseByRouteDirection routes start clause).literals.map
            PeriodicLiteral.atom) by rfl,
        countEq]
      exact congrArg₂ (· ++ ·) rfl (induction (start + 1))

/-- Clockwise clause sorting does not change the sequence of clause indices
at which a fixed atom occurs. -/
theorem orderClausesByRouteDirection_occurrenceClauseIndices
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) (atom : Variable) :
    occurrenceClauseIndices
        (orderClausesByRouteDirection source routes) atom =
      occurrenceClauseIndices source atom := by
  rw [occurrenceClauseIndices_eq, occurrenceClauseIndices_eq]
  unfold orderClausesByRouteDirection
  exact orderedOccurrenceCounts routes atom source.clauses 0

/-- A successful occurrence lookup after sorting has a source occurrence in
the same slot and source clause. -/
theorem exists_source_occurrenceAt_of_ordered
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (ordered : PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable)
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (orderClausesByRouteDirection source routes).erase atom slot =
        some ordered) :
    ∃ sourceTagged :
        PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable,
      PeriodicOneInThreeToThreeDM.occurrenceAt
          source.erase atom slot = some sourceTagged ∧
        sourceTagged.2.1 = ordered.2.1 := by
  have orderedClauseLookup :
      (occurrenceClauseIndices
        (orderClausesByRouteDirection source routes) atom)[slot.index]? =
        some ordered.2.1 := by
    have mapped := congrArg
      (Option.map fun tagged => tagged.2.1) lookup
    simpa [occurrenceClauseIndices,
      PeriodicOneInThreeToThreeDM.occurrenceAt] using mapped
  rw [orderClausesByRouteDirection_occurrenceClauseIndices
    source routes atom] at orderedClauseLookup
  unfold occurrenceClauseIndices at orderedClauseLookup
  rw [List.getElem?_map, Option.map_eq_some_iff] at orderedClauseLookup
  rcases orderedClauseLookup with
    ⟨sourceTagged, sourceLookup, clauseIndexEq⟩
  exact ⟨sourceTagged, sourceLookup, clauseIndexEq⟩

omit [DecidableEq Variable] in
private theorem exists_positionedOccurrence_of_tagged
    (source : PositionedPeriodicCNF Variable)
    {tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable}
    (taggedMember :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source.erase) :
    ∃ clause : PositionedPeriodicClause Variable,
      (clause, tagged.2.1) ∈ source.clauses.zipIdx ∧
        (tagged.1, tagged.2.2) ∈ clause.literals.zipIdx := by
  simp only [PeriodicThreeSATThree.taggedLiterals,
    List.mem_flatMap, List.mem_map] at taggedMember
  rcases taggedMember with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteral, taggedLiteralMember, taggedEqual⟩
  have clauseMember :
      (taggedClause.1, taggedClause.2) ∈
        source.erase.clauses.zipIdx :=
    taggedClauseMember
  change
    (taggedClause.1, taggedClause.2) ∈
      (source.clauses.map
        PositionedPeriodicClause.literals).zipIdx
    at clauseMember
  rw [List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨positionedTagged, positionedTaggedMember,
      positionedTaggedEqual⟩
  have clauseIndexEqual :
      positionedTagged.2 = taggedClause.2 :=
    congrArg Prod.snd positionedTaggedEqual
  have literalsEqual :
      positionedTagged.1.literals = taggedClause.1 := by
    simpa using congrArg Prod.fst positionedTaggedEqual
  subst tagged
  refine ⟨positionedTagged.1, ?_, ?_⟩
  · simpa only [← clauseIndexEqual] using positionedTaggedMember
  · rw [literalsEqual]
    exact taggedLiteralMember

private theorem value_eq_of_mem_zipIdx_same_index
    {Value : Type*} {values : List Value}
    {first second : Value} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second := by
  exact
    (List.mem_zipIdx' firstMember).2.trans
      (List.mem_zipIdx' secondMember).2.symm

/-- At any fixed occurrence slot, the sorted canonical route has the final
direction of the corresponding source route. -/
theorem
    orderCanonicalRoutesByClauseDirection_lastDirection_of_occurrenceAt
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (sourceDistinct : source.AllAtomsNodup)
    (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (ordered : PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable)
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (orderClausesByRouteDirection source routes).erase atom slot =
        some ordered) :
    ∃ sourceTagged :
        PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable,
      PeriodicOneInThreeToThreeDM.occurrenceAt
          source.erase atom slot = some sourceTagged ∧
        AxisDirection.polylineLastDirection
            (orderCanonicalRoutesByClauseDirection
              source placement routes ordered.2.1 ordered.2.2) =
          AxisDirection.polylineLastDirection
            (routes sourceTagged.2.1 sourceTagged.2.2) := by
  rcases exists_source_occurrenceAt_of_ordered
      source routes atom slot ordered lookup with
    ⟨sourceTagged, sourceLookup, clauseIndexEq⟩
  have orderedInfo :=
    PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      (orderClausesByRouteDirection source routes).erase
      atom slot ordered lookup
  have sourceInfo :=
    PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase atom slot sourceTagged sourceLookup
  rcases exists_positionedOccurrence_of_tagged
      (orderClausesByRouteDirection source routes) orderedInfo.1 with
    ⟨orderedClause, orderedClauseMember, orderedLiteralMember⟩
  rcases exists_positionedOccurrence_of_tagged source sourceInfo.1 with
    ⟨sourceClause, sourceClauseMember, sourceLiteralMember⟩
  rcases exists_sourceLiteral_of_orderedLiteral_mem
      routes orderedClauseMember orderedLiteralMember with
    ⟨recoveredClause, recoveredLiteral, recoveredLiteralIndex,
      recoveredClauseMember, recoveredLiteralMember,
      orderedClauseEq, orderedLiteralEq, orderedRouteEq⟩
  have clausesEq : recoveredClause = sourceClause :=
    value_eq_of_mem_zipIdx_same_index
      recoveredClauseMember (by simpa [clauseIndexEq] using sourceClauseMember)
  subst recoveredClause
  have sourceLiteralsNodup : sourceClause.literals.Nodup :=
    (sourceDistinct sourceClause
      (List.fst_mem_of_mem_zipIdx sourceClauseMember)).of_map
        PeriodicLiteral.atom
  have atomsNodup :=
    sourceDistinct sourceClause
      (List.fst_mem_of_mem_zipIdx sourceClauseMember)
  unfold PositionedPeriodicClause.AtomsNodup at atomsNodup
  have recoveredSourceLiteralEq :
      recoveredLiteral = sourceTagged.1 := by
    apply
      ((List.nodup_map_iff_inj_on sourceLiteralsNodup).mp atomsNodup)
        recoveredLiteral
        (List.fst_mem_of_mem_zipIdx recoveredLiteralMember)
        sourceTagged.1
        (List.fst_mem_of_mem_zipIdx sourceLiteralMember)
    rw [← orderedLiteralEq, orderedInfo.2, sourceInfo.2]
  have recoveredParts := List.mem_zipIdx' recoveredLiteralMember
  have sourceParts := List.mem_zipIdx' sourceLiteralMember
  have literalIndexEq :
      recoveredLiteralIndex = sourceTagged.2.2 := by
    apply
      (sourceLiteralsNodup.getElem_inj_iff
        (hi := recoveredParts.1) (hj := sourceParts.1)).mp
    rw [← recoveredParts.2, ← sourceParts.2,
      recoveredSourceLiteralEq]
  refine ⟨sourceTagged, sourceLookup, ?_⟩
  have sourceClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp sourceClauseMember
  have orderedRouteEq' :
      orderRoutesByClauseDirection source routes
          sourceTagged.2.1 ordered.2.2 =
        routes sourceTagged.2.1 recoveredLiteralIndex := by
    simpa [clauseIndexEq] using orderedRouteEq
  rw [← clauseIndexEq, orderCanonicalRoutesByClauseDirection,
    sourceClauseLookup, orderedRouteEq']
  simp [literalIndexEq]

/-- Reindexing canonical routes through a per-clause clockwise sort preserves
the variable-side occurrence rotation invariant. -/
theorem
    orderCanonicalRoutesByClauseDirection_variableRoutesInOccurrenceOrder
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceOrder : source.VariableRoutesInOccurrenceOrder routes) :
    (orderClausesByRouteDirection source routes).VariableRoutesInOccurrenceOrder
      (orderCanonicalRoutesByClauseDirection
        source placement routes) := by
  intro atom first second third
    firstLookup secondLookup thirdLookup
  rcases
      orderCanonicalRoutesByClauseDirection_lastDirection_of_occurrenceAt
        source placement routes sourceDistinct atom .first
        first firstLookup with
    ⟨sourceFirst, sourceFirstLookup, firstDirection⟩
  rcases
      orderCanonicalRoutesByClauseDirection_lastDirection_of_occurrenceAt
        source placement routes sourceDistinct atom .second
        second secondLookup with
    ⟨sourceSecond, sourceSecondLookup, secondDirection⟩
  rcases
      orderCanonicalRoutesByClauseDirection_lastDirection_of_occurrenceAt
        source placement routes sourceDistinct atom .third
        third thirdLookup with
    ⟨sourceThird, sourceThirdLookup, thirdDirection⟩
  have clockwise :=
    sourceOrder atom sourceFirst sourceSecond sourceThird
      sourceFirstLookup sourceSecondLookup sourceThirdLookup
  rw [firstDirection, secondDirection, thirdDirection]
  exact clockwise

end PositionedPeriodicCNF
end LeanTrominoes
