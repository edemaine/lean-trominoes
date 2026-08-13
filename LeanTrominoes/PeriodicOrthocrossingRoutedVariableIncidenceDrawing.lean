/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVariablePortGeometry
import LeanTrominoes.PlanarThreeSATDuplicatorArmIncidenceDrawing
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Routed-variable incidence drawings

Each active variable-fanout terminal is connected to the shared variable
center by a translated copy of its certified two-clause duplicator arm.
The physical arm stored in clause metadata chooses the template; the
enumeration index remains available separately for exact formula lookup.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Rename the endpoint and center roles of one fixed arm to the endpoints
of its active routed-variable equality link. -/
def planarSATRoutedVariableMap
    {Variable : Type*}
    (link : EqualityLink (PlanarSATNode Variable)) :
    DuplicatorArmVariable → PlanarSATVariable Variable
  | .port => .inl link.first
  | .center => .inl link.second

/-- An active link records equality-clause coordinates for the arm selected
by its external terminal. -/
theorem routedVariableLink_positions
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site) :
    link.positions =
      routedVariableEqualityPositions formula site
        link.first.duplicatorArm := by
  rcases List.mem_map.mp linkMem with
    ⟨taggedNode, taggedNodeMem, linkEq⟩
  subst link
  rfl

/-- The two logical roles of an active arm remain distinct after embedding
into the combined planar-SAT variable type. -/
theorem planarSATRoutedVariableMap_injective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site) :
    Function.Injective (planarSATRoutedVariableMap link) := by
  have endpointNe :=
    routedVariableLink_first_ne_second formula site linkMem
  have reverseNe : link.second ≠ link.first :=
    Ne.symm endpointNe
  intro first second equal
  cases first <;> cases second <;>
    simp_all [planarSATRoutedVariableMap]

/-- The final planar-SAT placement realizes the translated fixed-template
position of both roles in an active arm. -/
theorem planarSATRoutedVariableMap_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site)
    (armEq : arm = link.first.duplicatorArm)
    (role : DuplicatorArmVariable) :
    drawingPlanarSATVariablePosition formula
        (planarSATRoutedVariableMap link role) =
      Cell.add (routedVariableOrigin formula site)
        (DuplicatorArmVariable.position arm role) := by
  subst arm
  cases role with
  | port =>
      exact routedVariableLink_first_position
        formula wellFormed site linkMem
  | center =>
      exact routedVariableLink_second_position
        formula site linkMem

/-- Translate and rename the certified drawing of one active duplicator arm
into its routed variable macrocell. -/
def drawingPlanarSATRoutedVariableIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable) :=
  ((duplicatorArmStraightIncidenceDrawing arm).translate
      (routedVariableOrigin formula site)).rename
    (planarSATRoutedVariableMap link)
    (drawingPlanarSATVariablePosition formula)

/-- The placed drawing contains exactly the active equality clause block
recorded by the global clause index. -/
@[simp] theorem drawingPlanarSATRoutedVariableIncidenceDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (linkMem : link ∈ routedVariableLinksAt formula site)
    (armEq : arm = link.first.duplicatorArm) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site arm link).formula =
      drawingPlanarSATRoutedVariableFormulaAt link := by
  have positions :=
    routedVariableLink_positions formula site linkMem
  subst arm
  unfold drawingPlanarSATRoutedVariableFormulaAt
  rw [positions]
  simp [drawingPlanarSATRoutedVariableIncidenceDrawing,
    duplicatorArmStraightIncidenceDrawing,
    straightIncidenceDrawing, duplicatorArmFormula,
    routedVariableEqualityPositions,
    planarSATRoutedVariableMap, planarSATExternalVariableMap,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedClause.translate, EmbeddedClause.rename,
    EmbeddedClause.map, equalityInstance,
    Cell.add]

/-- Every placed arm route has its advertised clause and final planar-SAT
variable endpoints. -/
theorem drawingPlanarSATRoutedVariableIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site)
    (armEq : arm = link.first.duplicatorArm) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site arm link).RoutesMatch := by
  apply EmbeddedCNFIncidenceDrawing.routesMatch_rename
  · intro role roleMember
    simpa [EmbeddedCNFIncidenceDrawing.translate,
      duplicatorArmStraightIncidenceDrawing,
      straightIncidenceDrawing] using
      planarSATRoutedVariableMap_position
        formula wellFormed site arm linkMem armEq role
  · exact EmbeddedCNFIncidenceDrawing.routesMatch_translate
      (duplicatorArmStraightIncidenceDrawing_routesMatch arm)
      (routedVariableOrigin formula site)

/-- Translation and injective endpoint scoping preserve one active arm's
continuous finite planarity. -/
theorem drawingPlanarSATRoutedVariableIncidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site)
    (armEq : arm = link.first.duplicatorArm) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site arm link).IsPlanar := by
  apply EmbeddedCNFIncidenceDrawing.isPlanar_rename
  · intro first firstMember second secondMember equal
    exact planarSATRoutedVariableMap_injective
      formula site linkMem equal
  · intro role roleMember
    simpa [EmbeddedCNFIncidenceDrawing.translate,
      duplicatorArmStraightIncidenceDrawing,
      straightIncidenceDrawing] using
      planarSATRoutedVariableMap_position
        formula wellFormed site arm linkMem armEq role
  · exact EmbeddedCNFIncidenceDrawing.isPlanar_translate
      (duplicatorArmStraightIncidenceDrawing_isPlanar arm)
      (routedVariableOrigin formula site)

/-- Every placed active-arm incidence retains its fixed eight-direction
compass terminal ray. -/
theorem
    drawingPlanarSATRoutedVariableIncidenceDrawing_embeddedTerminalPortsValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site)
    (armEq : arm = link.first.duplicatorArm) :
    EmbeddedTerminalPortsValid
      (drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site arm link).formula
      (drawingPlanarSATVariablePosition formula) := by
  simpa [drawingPlanarSATRoutedVariableIncidenceDrawing,
    duplicatorArmStraightIncidenceDrawing,
    straightIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedClause.translate,
    EmbeddedClause.place, EmbeddedClause.rename,
    EmbeddedClause.map, instantiateFormula,
    Function.comp_def, Cell.add, Cell.scale] using
    (EmbeddedTerminalPortsValid.instantiateFormula
      (duplicatorArmFormula arm)
      (DuplicatorArmVariable.position arm)
      (planarSATRoutedVariableMap link)
      (routedVariableOrigin formula site)
      (factor := 1) (by norm_num)
      (drawingPlanarSATVariablePosition formula)
      (fun role => by
        simpa [Cell.scale] using
          planarSATRoutedVariableMap_position
            formula wellFormed site arm linkMem armEq role)
      (duplicatorArmFormula_embeddedTerminalPortsValid arm))

end PeriodicOrthocrossing
end LeanTrominoes
