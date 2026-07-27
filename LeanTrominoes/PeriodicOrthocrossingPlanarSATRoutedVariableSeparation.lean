import LeanTrominoes.PeriodicOrthocrossingPlanarSATMacrocellCenters
import LeanTrominoes.PlanarThreeSATDuplicatorArmSeparation

/-!
# Separation of routed-variable macrocells

Distinct active arms may intentionally share one lifted variable center.
Their route geometry is nevertheless the translated geometry of distinct
arms in the certified finite routed-duplicator star.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every clause index in a placed active-arm formula is below two. -/
theorem drawingPlanarSATRoutedVariableFormulaAt_clauseIndex_lt_two
    {Variable : Type*}
    (link : EqualityLink (PlanarSATNode Variable))
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx) :
    clauseIndex < 2 := by
  have indexLt :=
    List.snd_lt_of_mem_zipIdx clauseMember
  simpa [drawingPlanarSATRoutedVariableFormulaAt,
    equalityInstance] using indexLt

/-- Every clause in a placed active-arm formula is binary. -/
theorem drawingPlanarSATRoutedVariableFormulaAt_literalIndex_lt_two
    {Variable : Type*}
    (link : EqualityLink (PlanarSATNode Variable))
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    literalIndex < 2 := by
  simp [drawingPlanarSATRoutedVariableFormulaAt,
    equalityInstance] at clauseMember
  rcases clauseMember with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simpa [EmbeddedClause.rename, EmbeddedClause.map] using
      List.snd_lt_of_mem_zipIdx literalMember

/-- At one routed variable site, selected routes of two distinct physical
arms avoid one another after their common translation and logical renaming. -/
theorem
    drawingPlanarSATRoutedVariableIncidenceDrawing_routesAvoidEachOther_of_arms_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (firstArm secondArm : DuplicatorArm)
    (firstLink secondLink :
      EqualityLink (PlanarSATNode Variable))
    (differentArms : firstArm ≠ secondArm)
    (firstClauseIndex secondClauseIndex : Nat)
    (firstLiteralIndex secondLiteralIndex : Nat)
    (firstClauseIndexLt : firstClauseIndex < 2)
    (secondClauseIndexLt : secondClauseIndex < 2)
    (firstLiteralIndexLt : firstLiteralIndex < 2)
    (secondLiteralIndexLt : secondLiteralIndex < 2) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site firstArm firstLink).routes
        firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site secondArm secondLink).routes
        secondClauseIndex secondLiteralIndex) := by
  have base :=
    duplicatorArmStraightIncidenceDrawing_routesAvoidEachOther_of_ne
      firstArm secondArm differentArms
      firstClauseIndex secondClauseIndex
      firstLiteralIndex secondLiteralIndex
      firstClauseIndexLt secondClauseIndexLt
      firstLiteralIndexLt secondLiteralIndexLt
  have translated :=
    EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_translate
      base (routedVariableOrigin formula site)
  simpa [drawingPlanarSATRoutedVariableIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate] using translated

/-- Two distinct routed-variable components sharing one lifted variable
center must use distinct physical arms, whose selected routes are separated
by the finite duplicator-star certificate. -/
theorem drawingPlanarSATRoutedVariableMetadata_routesAvoidEachOther_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstSite secondSite : VariableRouteSite Variable}
    {firstArmIndex secondArmIndex : Nat}
    {firstArm secondArm : DuplicatorArm}
    {firstLink secondLink :
      EqualityLink (PlanarSATNode Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstValid :
      (⟨firstClause,
        .routedVariable firstSite firstArmIndex firstArm
          firstLink firstClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).Valid formula)
    (secondValid :
      (⟨secondClause,
        .routedVariable secondSite secondArmIndex secondArm
          secondLink secondClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).Valid formula)
    (sameCenter :
      liftedIncidenceVertexPosition formula
          (.variable firstSite.1) firstSite.2 =
        liftedIncidenceVertexPosition formula
          (.variable secondSite.1) secondSite.2)
    (differentComponents :
      DrawingPlanarSATComponent.routedVariable
          firstSite firstArm firstLink ≠
        DrawingPlanarSATComponent.routedVariable
          secondSite secondArm secondLink)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
          formula firstSite firstArm firstLink).routes
        firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
          formula secondSite secondArm secondLink).routes
        secondClauseIndex secondLiteralIndex) := by
  have firstSiteMem :
      firstSite ∈ drawingVariableRouteSites formula :=
    firstValid.1
  have secondSiteMem :
      secondSite ∈ drawingVariableRouteSites formula :=
    secondValid.1
  have sitesEqual :
      firstSite = secondSite :=
    liftedVariableRouteSite_eq
      formula firstSiteMem secondSiteMem sameCenter
  subst secondSite
  have firstLinkMem :
      firstLink ∈ routedVariableLinksAt formula firstSite :=
    List.fst_mem_of_mem_zipIdx firstValid.2.1
  have secondLinkMem :
      secondLink ∈ routedVariableLinksAt formula firstSite :=
    List.fst_mem_of_mem_zipIdx secondValid.2.1
  have differentArms : firstArm ≠ secondArm := by
    intro armsEqual
    have classifiedArmsEqual :
        firstLink.first.duplicatorArm =
          secondLink.first.duplicatorArm :=
      firstValid.2.2.1.symm.trans
        (armsEqual.trans secondValid.2.2.1)
    have linksEqual :
        firstLink = secondLink :=
      routedVariableLinksAt_eq_of_duplicatorArm_eq
        formula wellFormed degree firstSite
        firstLinkMem secondLinkMem classifiedArmsEqual
    subst secondLink
    have armsEqual' : firstArm = secondArm :=
      firstValid.2.2.1.trans secondValid.2.2.1.symm
    subst secondArm
    exact differentComponents rfl
  apply
    drawingPlanarSATRoutedVariableIncidenceDrawing_routesAvoidEachOther_of_arms_ne
      formula firstSite firstArm secondArm firstLink secondLink
      differentArms firstClauseIndex secondClauseIndex
      firstLiteralIndex secondLiteralIndex
  · exact
      drawingPlanarSATRoutedVariableFormulaAt_clauseIndex_lt_two
        firstLink firstValid.2.2.2
  · exact
      drawingPlanarSATRoutedVariableFormulaAt_clauseIndex_lt_two
        secondLink secondValid.2.2.2
  · exact
      drawingPlanarSATRoutedVariableFormulaAt_literalIndex_lt_two
        firstLink firstValid.2.2.2 firstLiteralMember
  · exact
      drawingPlanarSATRoutedVariableFormulaAt_literalIndex_lt_two
        secondLink secondValid.2.2.2 secondLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
