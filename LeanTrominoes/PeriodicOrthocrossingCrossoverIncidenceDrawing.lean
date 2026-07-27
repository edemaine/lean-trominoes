import LeanTrominoes.PeriodicCNFPlanarSATClauseIndex
import LeanTrominoes.PeriodicCNFPlanarSATGeometry
import LeanTrominoes.PlanarThreeSATIncidencePlanarity
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Crossover incidence drawings in the finite planar-SAT block

This module places the continuously planar direct Figure 8(b) drawing at one
canonical crossing and renames it into the final `PlanarSATVariable` type.
It identifies the resulting formula and every physical variable position
exactly, while retaining endpoint, planarity, and compass-terminal
certificates.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Rename every fixed Figure 8(b) role to the corresponding boundary or
crossing-scoped internal in the combined planar-SAT variable type. -/
def planarSATCrossoverVariableMap
    {Variable : Type*}
    (crossing : CrossingRecord) :
    CrossoverVariable → PlanarSATVariable Variable :=
  planarSATCoreVariableMap ∘
    scopedCrossoverVariableMap crossing
      (carrierNodeCrossingPorts crossing)

/-- The scoped Figure 8(b) renaming is injective on all fixed roles. -/
theorem planarSATCrossoverVariableMap_injective
    {Variable : Type*}
    (crossing : CrossingRecord) :
    Function.Injective
      (@planarSATCrossoverVariableMap Variable crossing) := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [planarSATCrossoverVariableMap,
      planarSATCoreVariableMap,
      scopedCrossoverVariableMap,
      carrierNodeCrossingPorts]

/-- The final planar-SAT placement realizes every renamed crossover role at
the translated fixed-template position. -/
theorem planarSATCrossoverVariableMap_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (role : CrossoverVariable) :
    drawingPlanarSATVariablePosition formula
        (planarSATCrossoverVariableMap crossing role) =
      Cell.add (crossingMacroOrigin crossing)
        (CrossoverVariable.position role) := by
  cases role <;>
    simp [planarSATCrossoverVariableMap,
      planarSATCoreVariableMap,
      scopedCrossoverVariableMap,
      carrierNodeCrossingPorts,
      drawingPlanarSATVariablePosition,
      CarrierNode.position, CrossingBoundary.position,
      CrossingSide.localPosition, crossoverInternalVariable,
      crossingMacroOrigin, CrossoverVariable.position,
      Cell.add, Cell.scale]

/-- The direct Figure 8(b) incidence drawing translated to one canonical
crossing and renamed into the combined planar-SAT variable type. -/
def drawingPlanarSATCrossoverIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable) :=
  (crossoverStraightIncidenceDrawing.translate
      (crossingMacroOrigin crossing)).rename
    (planarSATCrossoverVariableMap crossing)
    (drawingPlanarSATVariablePosition formula)

/-- The placed drawing contains exactly the local crossover clause block
recorded by the global clause index. -/
@[simp] theorem drawingPlanarSATCrossoverIncidenceDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    (drawingPlanarSATCrossoverIncidenceDrawing formula crossing).formula =
      drawingPlanarSATCrossoverFormulaAt
        (Variable := Variable) crossing := by
  simp [drawingPlanarSATCrossoverIncidenceDrawing,
    drawingPlanarSATCrossoverFormulaAt,
    planarSATCrossoverVariableMap,
    crossoverStraightIncidenceDrawing,
    straightIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedClause.translate,
    scopedCrossoverInstance,
    instantiateFormula,
    EmbeddedClause.place,
    EmbeddedClause.rename,
    EmbeddedClause.map,
    Function.comp_def, Cell.add, Cell.scale]

/-- Every placed crossover route has its advertised clause and final
planar-SAT variable endpoints. -/
theorem drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    (drawingPlanarSATCrossoverIncidenceDrawing formula crossing).RoutesMatch := by
  apply EmbeddedCNFIncidenceDrawing.routesMatch_rename
  · intro atom atomMember
    simpa [EmbeddedCNFIncidenceDrawing.translate,
      crossoverStraightIncidenceDrawing,
      straightIncidenceDrawing] using
      planarSATCrossoverVariableMap_position
        formula crossing atom
  · exact EmbeddedCNFIncidenceDrawing.routesMatch_translate
      crossoverStraightIncidenceDrawing_routesMatch
      (crossingMacroOrigin crossing)

/-- Translation and injective scoping preserve the fixed crossover's
continuous finite planarity. -/
theorem drawingPlanarSATCrossoverIncidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    (drawingPlanarSATCrossoverIncidenceDrawing formula crossing).IsPlanar := by
  apply EmbeddedCNFIncidenceDrawing.isPlanar_rename
  · intro first firstMember second secondMember equal
    exact planarSATCrossoverVariableMap_injective crossing equal
  · intro atom atomMember
    simpa [EmbeddedCNFIncidenceDrawing.translate,
      crossoverStraightIncidenceDrawing,
      straightIncidenceDrawing] using
      planarSATCrossoverVariableMap_position
        formula crossing atom
  · exact EmbeddedCNFIncidenceDrawing.isPlanar_translate
      crossoverStraightIncidenceDrawing_isPlanar
      (crossingMacroOrigin crossing)

/-- Every placed crossover incidence retains its fixed eight-direction
compass terminal ray. -/
theorem drawingPlanarSATCrossoverIncidenceDrawing_embeddedTerminalPortsValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    EmbeddedTerminalPortsValid
      (drawingPlanarSATCrossoverIncidenceDrawing formula crossing).formula
      (drawingPlanarSATVariablePosition formula) := by
  rw [drawingPlanarSATCrossoverIncidenceDrawing_formula]
  simpa [drawingPlanarSATCrossoverFormulaAt,
    scopedCrossoverInstance, planarSATCrossoverVariableMap,
    instantiateFormula, EmbeddedClause.place,
    EmbeddedClause.rename, EmbeddedClause.map,
    List.map_map, Function.comp_def] using
    (EmbeddedTerminalPortsValid.instantiateFormula
      crossoverFormula CrossoverVariable.position
      (planarSATCrossoverVariableMap crossing)
      (crossingMacroOrigin crossing)
      (factor := 1) (by norm_num)
      (drawingPlanarSATVariablePosition formula)
      (fun role => by
        simpa [Cell.scale] using
          planarSATCrossoverVariableMap_position
            formula crossing role)
      crossoverFormula_embeddedTerminalPortsValid)

end PeriodicOrthocrossing
end LeanTrominoes
