import LeanTrominoes.PlanarThreeSATDuplicatorArmIncidenceDrawing

/-!
# Separation between routed duplicator arms

The complete Figure 8(a) star is already certified planar.  The periodic
construction selects each active arm as its own two-clause drawing, so this
file records the corresponding finite pairwise certificate directly: any
genuine route of one physical arm avoids any genuine route of a different
physical arm.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Every local clause index of one active arm is below two. -/
theorem duplicatorArmFormula_clauseIndex_lt_two
    (arm : DuplicatorArm)
    {clause : EmbeddedClause DuplicatorArmVariable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (duplicatorArmFormula arm).zipIdx) :
    clauseIndex < 2 := by
  have indexLt :=
    List.snd_lt_of_mem_zipIdx clauseMember
  simpa [duplicatorArmFormula, equalityInstance] using indexLt

/-- Every active-arm clause is binary, so each genuine literal index is
below two. -/
theorem duplicatorArmFormula_literalIndex_lt_two
    (arm : DuplicatorArm)
    {clause : EmbeddedClause DuplicatorArmVariable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (duplicatorArmFormula arm).zipIdx)
    {literal : DuplicatorArmVariable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    literalIndex < 2 := by
  cases arm <;>
    simp [duplicatorArmFormula, equalityInstance] at clauseMember <;>
    rcases clauseMember with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp at literalMember <;>
    omega

/-- Any direct incidence routes belonging to different physical duplicator
arms avoid one another.  Each arm has exactly two binary local clauses, so
the certificate checks every selected incidence pair. -/
theorem duplicatorArmStraightIncidenceDrawing_routesAvoidEachOther_of_ne
    (firstArm secondArm : DuplicatorArm)
    (differentArms : firstArm ≠ secondArm)
    (firstClauseIndex secondClauseIndex : Nat)
    (firstLiteralIndex secondLiteralIndex : Nat)
    (firstClauseIndexLt : firstClauseIndex < 2)
    (secondClauseIndexLt : secondClauseIndex < 2)
    (firstLiteralIndexLt : firstLiteralIndex < 2)
    (secondLiteralIndexLt : secondLiteralIndex < 2) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((duplicatorArmStraightIncidenceDrawing firstArm).routes
        firstClauseIndex firstLiteralIndex)
      ((duplicatorArmStraightIncidenceDrawing secondArm).routes
        secondClauseIndex secondLiteralIndex) := by
  cases firstArm <;> cases secondArm <;>
    simp_all
  all_goals
    interval_cases firstClauseIndex <;>
      interval_cases secondClauseIndex <;>
        interval_cases firstLiteralIndex <;>
          interval_cases secondLiteralIndex <;>
            native_decide

end PlanarThreeSAT
end LeanTrominoes
