import LeanTrominoes.RetainedAngularFanDirectSourcePrefixAtlas
import LeanTrominoes.PlanarThreeSATTerminalPortCertificates
import LeanTrominoes.PlanarThreeSATDuplicatorArmIncidenceDrawing
import LeanTrominoes.PlanarThreeSATRoutedClauseIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingCrossoverIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingRoutedClauseIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableIncidenceDrawing

/-!
# Matching the direct source atlas to local incidence profiles

The source-prefix atlas is indexed by the same local clause numbers as the
three direct component families.  This file checks that the number of atlas
entries matches each clause's literal count and that every entry's retained
terminal direction is exactly the direction classified from the
corresponding direct incidence route.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PeriodicThreeSATThree
open PeriodicOrthocrossing

/-- The fixed crossover clause selected by an atlas-local clause index. -/
def retainedDirectCrossoverClauseAt
    (clauseIndex : Fin 26) : EmbeddedClause CrossoverVariable :=
  crossoverFormula.get
    ⟨clauseIndex.val, by
      simpa [crossoverFormula] using clauseIndex.isLt⟩

/-- The fixed duplicator-arm clause selected by its atlas-local index. -/
def retainedDirectDuplicatorClauseAt
    (arm : DuplicatorArm)
    (clauseIndex : Fin 2) :
    EmbeddedClause DuplicatorArmVariable :=
  (duplicatorArmFormula arm).get
    ⟨clauseIndex.val, by
      cases arm <;>
        simpa [duplicatorArmFormula, equalityInstance]
          using clauseIndex.isLt⟩

/-- The three-port representative used to certify routed source-clause
directions.  Literal signs do not affect its geometry. -/
def retainedDirectRoutedClauseRepresentativeLiterals :
    List (DuplicatorArm × Bool) :=
  [(.left, false), (.middle, false), (.right, false)]

/-- Every crossover atlas profile has one entry for every literal of the
corresponding Figure 8(b) clause. -/
theorem retainedDirectCrossoverPrefixChoices_length :
    ∀ clauseIndex : Fin 26,
      (retainedDirectSourcePrefixChoices
        (.crossover clauseIndex)).length =
      (retainedDirectCrossoverClauseAt
        clauseIndex).literals.length := by
  native_decide

/-- Every crossover atlas entry carries the exact classified terminal
direction of its direct local incidence. -/
theorem retainedDirectCrossoverPrefixChoice_direction :
    ∀ (clauseIndex : Fin 26)
      (literalIndex :
        Fin (retainedDirectSourcePrefixChoices
          (.crossover clauseIndex)).length),
      (retainedDirectSourcePrefixChoiceAt
        (.crossover clauseIndex) literalIndex).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          (crossoverStraightIncidenceDrawing.routes
            clauseIndex.val literalIndex.val)) := by
  native_decide

/-- Translation and logical renaming do not change the crossover atlas
direction selected at an actual crossing macrocell. -/
theorem retainedDirectCrossoverPrefixChoice_positionedDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (clauseIndex : Fin 26)
    (literalIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.crossover clauseIndex)).length) :
    (retainedDirectSourcePrefixChoiceAt
      (.crossover clauseIndex) literalIndex).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((drawingPlanarSATCrossoverIncidenceDrawing
            formula crossing).routes
              clauseIndex.val literalIndex.val)) := by
  rw [retainedDirectCrossoverPrefixChoice_direction]
  change
    classifiedRetainedTerminalDirection
        (routeTerminalVector
          (crossoverStraightIncidenceDrawing.routes
            clauseIndex.val literalIndex.val)) =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          (translatePolyline
            (crossingMacroOrigin crossing)
            (crossoverStraightIncidenceDrawing.routes
              clauseIndex.val literalIndex.val)))
  rw [routeTerminalVector_translatePolyline]

/-- Every duplicator-arm atlas profile has one entry for each literal of the
corresponding implication clause. -/
theorem retainedDirectDuplicatorPrefixChoices_length :
    ∀ (arm : DuplicatorArm) (clauseIndex : Fin 2),
      (retainedDirectSourcePrefixChoices
        (.duplicator arm clauseIndex)).length =
      (retainedDirectDuplicatorClauseAt
        arm clauseIndex).literals.length := by
  native_decide

/-- Every duplicator-arm atlas entry carries the exact classified terminal
direction of its direct local incidence. -/
theorem retainedDirectDuplicatorPrefixChoice_direction :
    ∀ (arm : DuplicatorArm) (clauseIndex : Fin 2)
      (literalIndex :
        Fin (retainedDirectSourcePrefixChoices
          (.duplicator arm clauseIndex)).length),
      (retainedDirectSourcePrefixChoiceAt
        (.duplicator arm clauseIndex) literalIndex).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((duplicatorArmStraightIncidenceDrawing arm).routes
            clauseIndex.val literalIndex.val)) := by
  native_decide

/-- Translation and endpoint renaming do not change the duplicator-arm atlas
direction selected at an actual routed-variable macrocell. -/
theorem retainedDirectDuplicatorPrefixChoice_positionedDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (clauseIndex : Fin 2)
    (literalIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.duplicator arm clauseIndex)).length) :
    (retainedDirectSourcePrefixChoiceAt
      (.duplicator arm clauseIndex) literalIndex).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((drawingPlanarSATRoutedVariableIncidenceDrawing
            formula site arm link).routes
              clauseIndex.val literalIndex.val)) := by
  rw [retainedDirectDuplicatorPrefixChoice_direction]
  change
    classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((duplicatorArmStraightIncidenceDrawing arm).routes
            clauseIndex.val literalIndex.val)) =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          (translatePolyline
            (routedVariableOrigin formula site)
            ((duplicatorArmStraightIncidenceDrawing arm).routes
              clauseIndex.val literalIndex.val)))
  rw [routeTerminalVector_translatePolyline]

/-- The full routed-clause atlas contains its three possible physical arms. -/
theorem retainedDirectRoutedClausePrefixChoices_length :
    (retainedDirectSourcePrefixChoices
      .routedClause).length = 3 := by
  native_decide

/-- Routed-clause atlas entries carry the exact classified directions of the
left, middle, and right source arms. -/
theorem retainedDirectRoutedClausePrefixChoice_direction :
    ∀ literalIndex :
      Fin (retainedDirectSourcePrefixChoices
        .routedClause).length,
      (retainedDirectSourcePrefixChoiceAt
        .routedClause literalIndex).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((routedClausePortStraightIncidenceDrawing
            retainedDirectRoutedClauseRepresentativeLiterals).routes
              0 literalIndex.val)) := by
  native_decide

/-- Physical routed-clause arms select their corresponding full-atlas
positions. -/
def retainedDirectRoutedClauseArmIndex :
    DuplicatorArm →
      Fin (retainedDirectSourcePrefixChoices
        .routedClause).length
  | .left => ⟨0, by native_decide⟩
  | .middle => ⟨1, by native_decide⟩
  | .right => ⟨2, by native_decide⟩

/-- The three physical arms occupy different routed-clause atlas entries. -/
theorem retainedDirectRoutedClauseArmIndex_injective :
    Function.Injective retainedDirectRoutedClauseArmIndex := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [retainedDirectRoutedClauseArmIndex]

/-- Selecting a routed entry by physical arm recovers that arm's retained
terminal direction. -/
theorem retainedDirectRoutedClauseArmChoice_direction
    (arm : DuplicatorArm) :
    (retainedDirectSourcePrefixChoiceAt
      .routedClause
      (retainedDirectRoutedClauseArmIndex arm)).direction =
        .routedClause arm := by
  cases arm <;> native_decide

/-- The route at any valid presentation index in a routed source clause has
the exceptional retained direction named by that literal's physical arm. -/
theorem routedClausePortStraightIncidenceDrawing_direction
    (literals : List (DuplicatorArm × Bool))
    (literalIndex : Fin literals.length) :
    classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((routedClausePortStraightIncidenceDrawing
            literals).routes 0 literalIndex.val)) =
      .routedClause (literals.get literalIndex).1 := by
  generalize armEq :
    (literals.get literalIndex).1 = arm
  cases arm <;>
    simp_all [routedClausePortStraightIncidenceDrawing,
      routedClausePortFormula, straightIncidenceDrawing,
      straightIncidenceRoutes, straightIncidenceRoute,
      routeTerminalVector, gridPolylineSegments,
      classifiedRetainedTerminalDirection,
      retainedTerminalDirectionClassify,
      DuplicatorArm.portPosition,
      Cell.sub] <;>
    native_decide

/-- A genuine routed source-clause literal selects the atlas entry indexed
by its physical arm, independently of the clause's literal presentation
order. -/
theorem retainedDirectRoutedClauseArmChoice_positionedDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    (literalIndex :
      Fin (routedClausePortLiterals formula site).length) :
    (retainedDirectSourcePrefixChoiceAt
      .routedClause
      (retainedDirectRoutedClauseArmIndex
        ((routedClausePortLiterals formula site).get
          literalIndex).1)).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((drawingPlanarSATRoutedClauseIncidenceDrawing
            formula site).routes 0 literalIndex.val)) := by
  rw [retainedDirectRoutedClauseArmChoice_direction]
  rw [←
    routedClausePortStraightIncidenceDrawing_direction
      (routedClausePortLiterals formula site) literalIndex]
  change
    classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((routedClausePortStraightIncidenceDrawing
            (routedClausePortLiterals formula site)).routes
              0 literalIndex.val)) =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          (translatePolyline
            (routedClauseOrigin formula site)
            ((routedClausePortStraightIncidenceDrawing
              (routedClausePortLiterals formula site)).routes
                0 literalIndex.val)))
  rw [routeTerminalVector_translatePolyline]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
