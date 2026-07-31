import LeanTrominoes.RetainedAngularFanDirectSourcePrefixAtlas
import LeanTrominoes.PlanarThreeSATTerminalPortCertificates
import LeanTrominoes.PlanarThreeSATDuplicatorArmIncidenceDrawing
import LeanTrominoes.PlanarThreeSATRoutedClauseIncidenceDrawing

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

/-- Selecting a routed entry by physical arm recovers that arm's retained
terminal direction. -/
theorem retainedDirectRoutedClauseArmChoice_direction
    (arm : DuplicatorArm) :
    (retainedDirectSourcePrefixChoiceAt
      .routedClause
      (retainedDirectRoutedClauseArmIndex arm)).direction =
        .routedClause arm := by
  cases arm <;> native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
