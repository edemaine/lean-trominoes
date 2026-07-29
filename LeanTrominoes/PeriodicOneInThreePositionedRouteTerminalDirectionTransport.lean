import LeanTrominoes.PeriodicOneInThreePositionedRouteTerminalDirections
import LeanTrominoes.PeriodicOneInThreeVariableRouteOrderTransport

/-!
# Concrete terminal-direction transport through exact-one reductions

The inherited route selectors now carry exact source-occurrence provenance.
This file combines that provenance with the route-splicing endpoint-direction
lemmas to discharge `PreservesOriginalRouteTerminalDirections` for both
Figure 9 and unit elimination.
-/

namespace LeanTrominoes

private theorem pair_eq_of_mem_of_mem_of_fst_eq
    {First Second : Type*}
    (pairs : List (First × Second))
    (fstNodup : (pairs.map Prod.fst).Nodup)
    {first second : First × Second}
    (firstMember : first ∈ pairs)
    (secondMember : second ∈ pairs)
    (fstEq : first.1 = second.1) :
    first = second := by
  have pairsNodup : pairs.Nodup :=
    fstNodup.of_map Prod.fst
  exact
    ((List.nodup_map_iff_inj_on pairsNodup).mp fstNodup)
      first firstMember second secondMember fstEq

private theorem value_eq_of_mem_zipIdx_same_index
    {α : Type*} {values : List α}
    {first second : α} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second := by
  exact
    (List.mem_zipIdx' firstMember).2.trans
      (List.mem_zipIdx' secondMember).2.symm

private theorem exists_positionedOccurrence_of_tagged
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {tagged : PeriodicLiteral Variable × Nat × Nat}
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

namespace PeriodicOneInThreePositioned

theorem preservesOriginalRouteTerminalDirections_splicedRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    (sourceLength :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          2 ≤ (sourceRoutes
            sourceClauseIndex sourceLiteralIndex).length) :
    PreservesOriginalRouteTerminalDirections
      source sourceRoutes
      (splicedRoutes source sourcePlacement
        (inheritedRouteSuffixes
          source sourcePlacement sourceWidth sourceDistinct
          sourceRoutes sourceEndpoints sourceOrthogonal)) := by
  intro atom output sourceOccurrence pairMember
  let pairs :=
    PeriodicOneInThree.formulaOriginalOccurrencePairs
      source.erase atom
  have outputMember :
      output ∈
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (PeriodicOneInThree.formula source.erase) (.inl atom) := by
    rw [← PeriodicOneInThree.formulaOriginalOccurrencePairs_fst
      source.erase atom]
    exact List.mem_map.mpr
      ⟨(output, sourceOccurrence), pairMember, rfl⟩
  have outputTaggedMember :
      output ∈
        PeriodicThreeSATThree.taggedLiterals
          (PeriodicOneInThree.formula source.erase) :=
    (List.mem_filter.mp outputMember).1
  have outputAtom : output.1.atom = .inl atom := by
    simpa using (List.mem_filter.mp outputMember).2
  have outputTaggedPositioned :
      output ∈
        PeriodicThreeSATThree.taggedLiterals
          (formula source).erase := by
    simpa only [erase_formula] using outputTaggedMember
  rcases exists_positionedOccurrence_of_tagged
      (formula source) outputTaggedPositioned with
    ⟨clause, clauseMember, literalMember⟩
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember atom outputAtom with
    ⟨data, dataLookup⟩
  have generatedClauseEq :
      data.generatedClause = clause :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedClauseMember clauseMember
  have generatedLiteralEq :
      data.generatedLiteral = output.1 :=
    value_eq_of_mem_zipIdx_same_index
      (by
        simpa [generatedClauseEq] using
          data.generatedLiteralMember)
      literalMember
  have dataAtom : data.sourceLiteral.atom = atom := by
    have literalAtom := data.literalAtom
    rw [generatedLiteralEq] at literalAtom
    exact Sum.inl.inj
      (literalAtom.symm.trans outputAtom)
  have dataPairMember :
      (output,
        (data.sourceLiteral, data.sourceClauseIndex,
          data.sourceLiteralIndex)) ∈ pairs := by
    simpa [pairs, dataAtom, generatedLiteralEq] using
      data.originalOccurrencePair
  have pairsFstNodup : (pairs.map Prod.fst).Nodup := by
    rw [show
      pairs.map Prod.fst =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (PeriodicOneInThree.formula source.erase) (.inl atom) by
      simpa [pairs] using
        PeriodicOneInThree.formulaOriginalOccurrencePairs_fst
          source.erase atom]
    exact PeriodicOneInThreeToThreeDM.occurrencesOf_nodup _ _
  have pairEq :=
    pair_eq_of_mem_of_mem_of_fst_eq pairs pairsFstNodup
      dataPairMember pairMember rfl
  have sourceOccurrenceEq :
      (data.sourceLiteral, data.sourceClauseIndex,
        data.sourceLiteralIndex) = sourceOccurrence :=
    congrArg Prod.snd pairEq
  let inherited :=
    inheritedRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal
  have inheritedLength :
      2 ≤ (inherited.routes output.2.1 output.2.2).length := by
    simp [inherited, inheritedRouteSuffixes,
      inheritedRouteSuffixesRoutes, dataLookup,
      inheritedRouteSuffix, joinAtEndpoint,
      PositionedPeriodicCNF.orthogonalDetour]
  calc
    AxisDirection.polylineLastDirection
        (splicedRoutes source sourcePlacement inherited
          output.2.1 output.2.2) =
      AxisDirection.polylineLastDirection
        (inherited.routes output.2.1 output.2.2) :=
      splicedRoutes_lastDirection_inherited
        source sourcePlacement sourceWidth sourceDistinct
        inherited clauseMember literalMember atom outputAtom
        inheritedLength
    _ = AxisDirection.polylineLastDirection
          (sourceRoutes
            data.sourceClauseIndex data.sourceLiteralIndex) := by
      have inheritedRouteEq :
          inherited.routes output.2.1 output.2.2 =
            inheritedRouteSuffix
              (placement source sourcePlacement)
              sourcePlacement data.sourceClause data.generatedClause
              data.sourceLiteralIndex
              (sourceRoutes
                data.sourceClauseIndex data.sourceLiteralIndex) := by
        simp [inherited, inheritedRouteSuffixes,
          inheritedRouteSuffixesRoutes, dataLookup]
      rw [inheritedRouteEq]
      exact inheritedRouteSuffix_lastDirection
        (placement source sourcePlacement)
        sourcePlacement data.sourceClause data.generatedClause
        data.sourceLiteralIndex
        (sourceRoutes
          data.sourceClauseIndex data.sourceLiteralIndex)
        (sourceEndpoints
          data.sourceClause data.sourceClauseIndex
          data.sourceClauseMember
          data.sourceLiteral data.sourceLiteralIndex
          data.sourceLiteralMember).1
        (sourceLength
          data.sourceClause data.sourceClauseIndex
          data.sourceClauseMember
          data.sourceLiteral data.sourceLiteralIndex
          data.sourceLiteralMember)
    _ = AxisDirection.polylineLastDirection
          (sourceRoutes
            sourceOccurrence.2.1 sourceOccurrence.2.2) := by
      rw [← sourceOccurrenceEq]

end PeriodicOneInThreePositioned

namespace PeriodicOneInThreeNoUnitsPositioned

private theorem
    preservesOriginalRouteTerminalDirections_splicedRoutes_of
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit)
    (eligible : Variable → Prop)
    (sourceLength :
      ∀ atom,
        eligible atom →
        ∀ sourceClause sourceClauseIndex,
          (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
          ∀ sourceLiteral sourceLiteralIndex,
            (sourceLiteral, sourceLiteralIndex) ∈
                sourceClause.literals.zipIdx →
            sourceLiteral.atom = atom →
            3 ≤ (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).length) :
    ∀ atom output sourceOccurrence,
      eligible atom →
      (output, sourceOccurrence) ∈
          PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs
            source.erase atom →
      AxisDirection.polylineLastDirection
          (splicedRoutes source sourcePlacement
            (inheritedRouteSuffixes
              source sourcePlacement sourceWidth sourceDistinct
              sourceRoutes sourceEndpoints sourceOrthogonal sourceExits)
            output.2.1 output.2.2) =
        AxisDirection.polylineLastDirection
          (sourceRoutes
            sourceOccurrence.2.1 sourceOccurrence.2.2) := by
  intro atom output sourceOccurrence atomEligible pairMember
  let pairs :=
    PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs
      source.erase atom
  have outputMember :
      output ∈
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (PeriodicOneInThreeNoUnits.formula source.erase)
          (.inl atom) := by
    rw [←
      PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs_fst
        source.erase atom]
    exact List.mem_map.mpr
      ⟨(output, sourceOccurrence), pairMember, rfl⟩
  have outputTaggedMember :
      output ∈
        PeriodicThreeSATThree.taggedLiterals
          (PeriodicOneInThreeNoUnits.formula source.erase) :=
    (List.mem_filter.mp outputMember).1
  have outputAtom : output.1.atom = .inl atom := by
    simpa using (List.mem_filter.mp outputMember).2
  have outputTaggedPositioned :
      output ∈
        PeriodicThreeSATThree.taggedLiterals
          (formula source).erase := by
    simpa only [erase_formula] using outputTaggedMember
  rcases exists_positionedOccurrence_of_tagged
      (formula source) outputTaggedPositioned with
    ⟨clause, clauseMember, literalMember⟩
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember atom outputAtom with
    ⟨data, dataLookup⟩
  have generatedClauseEq :
      data.generatedClause = clause :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedClauseMember clauseMember
  have generatedLiteralEq :
      data.generatedLiteral = output.1 :=
    value_eq_of_mem_zipIdx_same_index
      (by
        simpa [generatedClauseEq] using
          data.generatedLiteralMember)
      literalMember
  have dataAtom : data.sourceLiteral.atom = atom := by
    have literalAtom := data.literalAtom
    rw [generatedLiteralEq] at literalAtom
    exact Sum.inl.inj
      (literalAtom.symm.trans outputAtom)
  have dataPairMember :
      (output,
        (data.sourceLiteral, data.sourceClauseIndex,
          data.sourceLiteralIndex)) ∈ pairs := by
    simpa [pairs, dataAtom, generatedLiteralEq] using
      data.originalOccurrencePair
  have pairsFstNodup : (pairs.map Prod.fst).Nodup := by
    rw [show
      pairs.map Prod.fst =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (PeriodicOneInThreeNoUnits.formula source.erase)
          (.inl atom) by
      simpa [pairs] using
        PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs_fst
          source.erase atom]
    exact PeriodicOneInThreeToThreeDM.occurrencesOf_nodup _ _
  have pairEq :=
    pair_eq_of_mem_of_mem_of_fst_eq pairs pairsFstNodup
      dataPairMember pairMember rfl
  have sourceOccurrenceEq :
      (data.sourceLiteral, data.sourceClauseIndex,
        data.sourceLiteralIndex) = sourceOccurrence :=
    congrArg Prod.snd pairEq
  let inherited :=
    inheritedRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
  have inheritedLength :
      2 ≤ (inherited.routes output.2.1 output.2.2).length := by
    simp [inherited, inheritedRouteSuffixes,
      inheritedRouteSuffixesRoutes, dataLookup,
      inheritedRouteSuffix, replacePolylineHead, joinAtEndpoint,
      PositionedPeriodicCNF.orthogonalDetour]
  calc
    AxisDirection.polylineLastDirection
        (splicedRoutes source sourcePlacement inherited
          output.2.1 output.2.2) =
      AxisDirection.polylineLastDirection
        (inherited.routes output.2.1 output.2.2) :=
      splicedRoutes_lastDirection_inherited
        source sourcePlacement sourceWidth sourceDistinct
        inherited clauseMember literalMember atom outputAtom
        inheritedLength
    _ = AxisDirection.polylineLastDirection
          (sourceRoutes
            data.sourceClauseIndex data.sourceLiteralIndex) := by
      have inheritedRouteEq :
          inherited.routes output.2.1 output.2.2 =
            inheritedRouteSuffix
              (placement source sourcePlacement)
              sourcePlacement data.sourceClause data.generatedClause
              data.sourceLiteralIndex
              (sourceRoutes
                data.sourceClauseIndex data.sourceLiteralIndex) := by
        simp [inherited, inheritedRouteSuffixes,
          inheritedRouteSuffixesRoutes, dataLookup]
      rw [inheritedRouteEq]
      exact inheritedRouteSuffix_lastDirection
        (placement source sourcePlacement)
        sourcePlacement data.sourceClause data.generatedClause
        data.sourceLiteralIndex
        (sourceRoutes
          data.sourceClauseIndex data.sourceLiteralIndex)
        (sourceLength
          atom atomEligible
          data.sourceClause data.sourceClauseIndex
          data.sourceClauseMember
          data.sourceLiteral data.sourceLiteralIndex
          data.sourceLiteralMember dataAtom)
    _ = AxisDirection.polylineLastDirection
          (sourceRoutes
            sourceOccurrence.2.1 sourceOccurrence.2.2) := by
      rw [← sourceOccurrenceEq]

/-- For degree-three source atoms, the unit-elimination splice preserves
the terminal direction of every inherited route. -/
theorem
    preservesDegreeThreeOriginalRouteTerminalDirections_splicedRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit)
    (sourceLength :
      ∀ atom sourceThird,
        PeriodicOneInThreeToThreeDM.occurrenceAt
            source.erase atom .third = some sourceThird →
        ∀ sourceClause sourceClauseIndex,
          (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
          ∀ sourceLiteral sourceLiteralIndex,
            (sourceLiteral, sourceLiteralIndex) ∈
                sourceClause.literals.zipIdx →
            sourceLiteral.atom = atom →
            3 ≤ (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).length) :
    PreservesDegreeThreeOriginalRouteTerminalDirections
      source sourceRoutes
      (splicedRoutes source sourcePlacement
        (inheritedRouteSuffixes
          source sourcePlacement sourceWidth sourceDistinct
          sourceRoutes sourceEndpoints sourceOrthogonal sourceExits)) := by
  intro atom sourceThird thirdLookup output sourceOccurrence pairMember
  apply
    preservesOriginalRouteTerminalDirections_splicedRoutes_of
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
      (fun atom =>
        ∃ third,
          PeriodicOneInThreeToThreeDM.occurrenceAt
              source.erase atom .third = some third)
      (fun atom degreeThree sourceClause sourceClauseIndex
          sourceClauseMember sourceLiteral sourceLiteralIndex
          sourceLiteralMember literalAtom =>
        sourceLength atom degreeThree.choose degreeThree.choose_spec
          sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember literalAtom)
      atom output sourceOccurrence
  · exact ⟨sourceThird, thirdLookup⟩
  · exact pairMember

/-- If every source route has at least three points, the unrestricted
unit-elimination preservation certificate follows as before. -/
theorem preservesOriginalRouteTerminalDirections_splicedRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit)
    (sourceLength :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          3 ≤ (sourceRoutes
            sourceClauseIndex sourceLiteralIndex).length) :
    PreservesOriginalRouteTerminalDirections
      source sourceRoutes
      (splicedRoutes source sourcePlacement
        (inheritedRouteSuffixes
          source sourcePlacement sourceWidth sourceDistinct
          sourceRoutes sourceEndpoints sourceOrthogonal sourceExits)) := by
  intro atom output sourceOccurrence pairMember
  apply
    preservesOriginalRouteTerminalDirections_splicedRoutes_of
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
      (fun _ => True)
      (fun _atom _eligible sourceClause sourceClauseIndex
          sourceClauseMember sourceLiteral sourceLiteralIndex
          sourceLiteralMember _literalAtom =>
        sourceLength sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember)
      atom output sourceOccurrence trivial pairMember

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
