import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPresentationProperties
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRoutedTriples
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreLocalGates

/-!
# Polarity-normalized formulas at the planar 3DM boundary

This file connects the formula-level polarity certificate to the occurrence
tables used by the planar 3DM construction.  Every active occurrence of a
width-three normalized formula selects one of the three endpoint-clear local
tables: fixed-red/false, fixed-blue/false, or fixed-green/true.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM
open PeriodicOneInThreePolarityNormalization

/-- Shifting each clause to zero anchor preserves its literal-value pattern. -/
theorem FormulaPolarityNormalized.anchorNormalize
    {Variable : Type*} {source : PeriodicCNF Variable}
    (normalized : FormulaPolarityNormalized source) :
    FormulaPolarityNormalized source.anchorNormalize := by
  unfold FormulaPolarityNormalized at normalized ⊢
  intro normalizedClause normalizedMember
  rcases List.mem_map.mp normalizedMember with
    ⟨sourceClause, sourceMember, rfl⟩
  unfold ClausePolarityNormalized at normalized ⊢
  simpa [PeriodicClause.anchorNormalize, List.map_map,
    Function.comp_def] using normalized sourceClause sourceMember

/-- A tagged occurrence inherits the requested polarity at its literal
index from the formula-level certificate. -/
theorem taggedOccurrence_value_eq_normalizedPolarity
    {Variable : Type*} (source : PeriodicCNF Variable)
    (normalized : FormulaPolarityNormalized source)
    (tagged : TaggedOccurrence Variable)
    (taggedMember :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    tagged.1.value = normalizedPolarity tagged.2.2 := by
  simp only [PeriodicThreeSATThree.taggedLiterals,
    List.mem_flatMap, List.mem_map] at taggedMember
  rcases taggedMember with
    ⟨taggedClause, clauseMember, taggedLiteral,
      literalMember, taggedEq⟩
  subst tagged
  exact literal_value_eq_normalizedPolarity_of_clause
    (normalized taggedClause.1
      (List.fst_mem_of_mem_zipIdx clauseMember)) literalMember

/-- A tagged occurrence of a width-three formula has literal index below
three. -/
theorem taggedOccurrence_literalIndex_lt_three
    {Variable : Type*} (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3)
    (tagged : TaggedOccurrence Variable)
    (taggedMember :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    tagged.2.2 < 3 := by
  simp only [PeriodicThreeSATThree.taggedLiterals,
    List.mem_flatMap, List.mem_map] at taggedMember
  rcases taggedMember with
    ⟨taggedClause, clauseMember, taggedLiteral,
      literalMember, taggedEq⟩
  subst tagged
  have literalLt : taggedLiteral.2 < taggedClause.1.length :=
    List.snd_lt_of_mem_zipIdx literalMember
  have clauseWidth : taggedClause.1.length ≤ 3 :=
    width taggedClause.1 (List.fst_mem_of_mem_zipIdx clauseMember)
  simpa using literalLt.trans_le clauseWidth

/-- Each of the three normalized literal positions selects an endpoint-clear
local connector table. -/
theorem connectorKind_normalizedPolarity_pattern
    (literalIndex : Nat) (indexLt : literalIndex < 3) :
    VariableLocalGateTableEndpointClear
        (connectorKindOfLiteralIndex literalIndex)
        (normalizedPolarity literalIndex) := by
  interval_cases literalIndex <;>
    decide

/-- Looking up an active occurrence in a normalized source recovers its
requested polarity. -/
theorem occurrencePolarity_eq_normalizedPolarity
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (normalized : FormulaPolarityNormalized source)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    occurrencePolarity source atom slot =
      normalizedPolarity (occurrenceLiteralIndex source atom slot) := by
  have taggedMember :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source atom slot tagged lookup).1
  calc
    occurrencePolarity source atom slot = tagged.1.value :=
      occurrencePolarity_of_occurrenceAt source atom slot tagged lookup
    _ = normalizedPolarity tagged.2.2 :=
      taggedOccurrence_value_eq_normalizedPolarity
        source normalized tagged taggedMember
    _ = normalizedPolarity (occurrenceLiteralIndex source atom slot) := by
      rw [occurrenceLiteralIndex_of_occurrenceAt
        source atom slot tagged lookup]

/-- Every active occurrence in a width-three normalized source has an
endpoint-clear local table. -/
theorem occurrenceConnectorPolarity_pattern
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    VariableLocalGateTableEndpointClear
        (occurrenceConnectorKind source atom slot)
        (occurrencePolarity source atom slot) := by
  have taggedMember :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source atom slot tagged lookup).1
  have indexLt : occurrenceLiteralIndex source atom slot < 3 := by
    rw [occurrenceLiteralIndex_of_occurrenceAt
      source atom slot tagged lookup]
    exact taggedOccurrence_literalIndex_lt_three
      source width tagged taggedMember
  have pattern := connectorKind_normalizedPolarity_pattern
    (occurrenceLiteralIndex source atom slot) indexLt
  rw [← occurrencePolarity_eq_normalizedPolarity
    source normalized atom slot tagged lookup] at pattern
  exact pattern

/-- Any active normalized occurrence, in particular one that is not
fixed-green, discharges the endpoint-clear local-gate hypothesis. -/
theorem occurrence_localGateTableEndpointClear_of_kind_ne_fixedGreen
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged)
    (_kindNe : occurrenceConnectorKind source atom slot ≠ .fixedGreen) :
    VariableLocalGateTableEndpointClear
      (occurrenceConnectorKind source atom slot)
      (occurrencePolarity source atom slot) := by
  exact occurrenceConnectorPolarity_pattern source width normalized
    atom slot tagged lookup

/-- Conversely, a fixed-green active occurrence in a normalized source is
always in the true orientation. -/
theorem occurrencePolarity_eq_true_of_connectorKind_eq_fixedGreen
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedGreen) :
    occurrencePolarity source atom slot = true := by
  rcases occurrenceConnectorPolarity_pattern source width normalized
      atom slot tagged lookup with clear | clear
  · exact (clear.2 kindEq).elim
  · exact clear.1

/-- The output of logical polarity normalization satisfies the connector
classification whenever the input already has binary-or-ternary clauses. -/
theorem normalizedFormula_occurrenceConnectorPolarity_pattern
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source)
    (atom : PolarityNormalizedVariable Variable)
    (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence (PolarityNormalizedVariable Variable))
    (lookup : occurrenceAt
      (PeriodicOneInThreePolarityNormalization.formula source)
      atom slot = some tagged) :
    VariableLocalGateTableEndpointClear
        (occurrenceConnectorKind
          (PeriodicOneInThreePolarityNormalization.formula source)
          atom slot)
        (occurrencePolarity
          (PeriodicOneInThreePolarityNormalization.formula source)
          atom slot) := by
  apply occurrenceConnectorPolarity_pattern
    (PeriodicOneInThreePolarityNormalization.formula source)
  · intro clause clauseMember
    change clause.length ≤ 3
    rcases formula_arityTwoOrThree arity clause clauseMember with
      clauseArity | clauseArity
    · omega
    · omega
  · exact formula_polarityNormalized source
  · exact lookup

/-- The geometrically routed polarity normalization has the same connector
classification at every active occurrence. -/
theorem routedNormalizedFormula_occurrenceConnectorPolarity_pattern
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (atom : PolarityNormalizedVariable Variable)
    (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence (PolarityNormalizedVariable Variable))
    (lookup : occurrenceAt
      (PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
        source sourcePlacement routes).erase
      atom slot = some tagged) :
    VariableLocalGateTableEndpointClear
        (occurrenceConnectorKind
          (PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
            source sourcePlacement routes).erase
          atom slot)
        (occurrencePolarity
          (PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
            source sourcePlacement routes).erase
          atom slot) := by
  apply occurrenceConnectorPolarity_pattern
    (PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
      source sourcePlacement routes).erase
  · exact
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula_widthAtMostThree
        source sourcePlacement routes arity
  · exact
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula_polarityNormalized
        source sourcePlacement routes
  · exact lookup

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
