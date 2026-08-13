/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarClausePortGeometry
import LeanTrominoes.PlanarThreeSATRoutedClauseIncidenceDrawing
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Routed source-clause incidence drawings

Each routed source clause is a translated subset of the certified
three-port clause star.  Its actual variables are the source terminals of
the corresponding incidence routes; renaming those variables to their
physical arms recovers the fixed local drawing exactly.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Signed physical arms of the incidences entering one routed source
clause, in the clause's literal order. -/
def routedClausePortLiterals
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    List (DuplicatorArm × Bool) :=
  (clauseRouteOccurrencesAt formula site).map fun occurrence =>
    (sourceOccurrenceArm formula occurrence,
      occurrence.incidence.literal.value)

/-- The signed port list of a degree-three routed clause has no repeated
physical arm. -/
theorem routedClausePortLiterals_ports_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (site : ClauseRouteSite) :
    ((routedClausePortLiterals formula site).map Prod.fst).Nodup := by
  change
    (((clauseRouteOccurrencesAt formula site).map fun occurrence =>
      (sourceOccurrenceArm formula occurrence,
        occurrence.incidence.literal.value)).map Prod.fst).Nodup
  rw [List.map_map]
  exact sourceOccurrenceArms_nodup formula degree site

/-- Origin of the clause macrocell containing one source-clause star. -/
def routedClauseOrigin
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) : Cell :=
  liftedIncidenceVertexMacroOrigin formula
    (.clause site.1) site.2

/-- Rename an actual routed-clause terminal to its local physical arm. -/
def planarSATRoutedClauseArm
    {Variable : Type*} :
    PlanarSATVariable Variable → DuplicatorArm
  | .inl node => node.duplicatorArm
  | .inr _ => .right

/-- Placed position of one local routed-clause arm. -/
def routedClauseArmPosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    (arm : DuplicatorArm) : Cell :=
  Cell.add (routedClauseOrigin formula site) arm.portPosition

/-- The actual routed source clause, equipped with the translated fixed-star
route family in the same literal presentation order. -/
def drawingPlanarSATRoutedClauseIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable) where
  formula :=
    [(routedClauseAt formula site).rename
      planarSATExternalVariableMap]
  variablePosition := drawingPlanarSATVariablePosition formula
  routes :=
    ((routedClausePortStraightIncidenceDrawing
      (routedClausePortLiterals formula site)).translate
        (routedClauseOrigin formula site)).routes

/-- The placed drawing contains exactly the singleton source clause recorded
by the global clause index. -/
@[simp] theorem drawingPlanarSATRoutedClauseIncidenceDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).formula =
      [(routedClauseAt formula site).rename
        planarSATExternalVariableMap] := by
  rfl

/-- Renaming an actual source-clause drawing by physical arm recovers the
translated fixed port-star drawing exactly. -/
theorem drawingPlanarSATRoutedClauseIncidenceDrawing_rename
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).rename
        planarSATRoutedClauseArm
        (routedClauseArmPosition formula site) =
      (routedClausePortStraightIncidenceDrawing
        (routedClausePortLiterals formula site)).translate
          (routedClauseOrigin formula site) := by
  unfold drawingPlanarSATRoutedClauseIncidenceDrawing
    routedClausePortStraightIncidenceDrawing
    EmbeddedCNFIncidenceDrawing.rename
    EmbeddedCNFIncidenceDrawing.translate
  congr 1
  simp [routedClausePortFormula, routedClausePortLiterals,
    routedClauseOrigin, routedClauseAt,
    straightIncidenceDrawing, planarSATRoutedClauseArm,
    PlanarSATNode.duplicatorArm,
    planarSATExternalVariableMap, sourceOccurrenceArm_eq,
    EmbeddedClause.rename, EmbeddedClause.map,
    EmbeddedClause.translate, List.map_map,
    Function.comp_def]

/-- Variables occurring in one source-clause drawing are precisely its
renamed source terminals. -/
theorem mem_drawingPlanarSATRoutedClause_variableVertices_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    (atom : PlanarSATVariable Variable) :
    atom ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).variableVertices ↔
      ∃ occurrence ∈ clauseRouteOccurrencesAt formula site,
        atom =
          .inl (.carrier
            (.terminal (occurrence.sourceTerminal formula))) := by
  simp [EmbeddedCNFIncidenceDrawing.variableVertices,
    drawingPlanarSATRoutedClauseIncidenceDrawing,
    routedClauseAt, planarSATExternalVariableMap,
    EmbeddedClause.rename, EmbeddedClause.map, eq_comm]

/-- Physical-arm renaming is injective on the variables actually occurring
in one degree-three routed source clause. -/
theorem planarSATRoutedClauseArm_injectiveOn
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (site : ClauseRouteSite)
    {first second : PlanarSATVariable Variable}
    (firstMember :
      first ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).variableVertices)
    (secondMember :
      second ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).variableVertices)
    (armEqual :
      planarSATRoutedClauseArm first =
        planarSATRoutedClauseArm second) :
    first = second := by
  rcases
      (mem_drawingPlanarSATRoutedClause_variableVertices_iff
        formula site first).mp firstMember with
    ⟨firstOccurrence, firstOccurrenceMember, rfl⟩
  rcases
      (mem_drawingPlanarSATRoutedClause_variableVertices_iff
        formula site second).mp secondMember with
    ⟨secondOccurrence, secondOccurrenceMember, rfl⟩
  have occurrenceEqual :
      firstOccurrence = secondOccurrence := by
    apply sourceOccurrenceArm_injective_on
      formula degree site
      firstOccurrenceMember secondOccurrenceMember
    simpa [planarSATRoutedClauseArm,
      PlanarSATNode.duplicatorArm,
      sourceOccurrenceArm_eq] using armEqual
  subst secondOccurrence
  rfl

/-- The final planar-SAT placement realizes each occurring routed-clause
variable at its translated fixed-star port. -/
theorem planarSATRoutedClauseArm_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : ClauseRouteSite)
    (atom : PlanarSATVariable Variable)
    (atomMember :
      atom ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).variableVertices) :
    routedClauseArmPosition formula site
        (planarSATRoutedClauseArm atom) =
      drawingPlanarSATVariablePosition formula atom := by
  rcases
      (mem_drawingPlanarSATRoutedClause_variableVertices_iff
        formula site atom).mp atomMember with
    ⟨occurrence, occurrenceMember, rfl⟩
  simpa [routedClauseArmPosition, routedClauseOrigin,
    planarSATRoutedClauseArm,
    PlanarSATNode.duplicatorArm,
    drawingPlanarSATVariablePosition,
    CarrierNode.position] using
    (occurrence.sourceTerminal_position_eq_routedClausePort
      formula wellFormed site occurrenceMember).symm

/-- Every placed source-clause route has its advertised clause and final
planar-SAT variable endpoints. -/
theorem drawingPlanarSATRoutedClauseIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : ClauseRouteSite) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).RoutesMatch := by
  apply EmbeddedCNFIncidenceDrawing.routesMatch_of_rename
    planarSATRoutedClauseArm
    (routedClauseArmPosition formula site)
  · exact planarSATRoutedClauseArm_position
      formula wellFormed site
  · rw [drawingPlanarSATRoutedClauseIncidenceDrawing_rename]
    exact EmbeddedCNFIncidenceDrawing.routesMatch_translate
      (routedClausePortStraightIncidenceDrawing_routesMatch
        (routedClausePortLiterals formula site))
      (routedClauseOrigin formula site)

/-- Every degree-three routed source-clause star is continuously planar. -/
theorem drawingPlanarSATRoutedClauseIncidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (site : ClauseRouteSite) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).IsPlanar := by
  apply EmbeddedCNFIncidenceDrawing.isPlanar_of_rename
    planarSATRoutedClauseArm
    (routedClauseArmPosition formula site)
  · intro first firstMember second secondMember armEqual
    exact planarSATRoutedClauseArm_injectiveOn
      formula degree site firstMember secondMember armEqual
  · exact planarSATRoutedClauseArm_position
      formula wellFormed site
  · rw [drawingPlanarSATRoutedClauseIncidenceDrawing_rename]
    exact EmbeddedCNFIncidenceDrawing.isPlanar_translate
      (routedClausePortStraightIncidenceDrawing_isPlanar
        (routedClausePortLiterals formula site)
        (routedClausePortLiterals_ports_nodup
          formula degree site))
      (routedClauseOrigin formula site)

end PeriodicOrthocrossing
end LeanTrominoes
