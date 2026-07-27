import LeanTrominoes.PositionedPeriodicCNFLocalRouteSplicing

/-!
# Completing local route suffixes over a source/auxiliary sum

Clause gadgets enlarge their variable type from `Source` to
`Source ⊕ Auxiliary`.  A newly introduced auxiliary already has its final
endpoint inside the local drawing, so its suffix can be the singleton splice
point.  Only inherited `.inl` variables need a nontrivial external suffix.

This file packages that reduced obligation and turns it into the uniform
canonical suffix family consumed by local-route splicing.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Orthogonal canonical suffixes required only for inherited source
variables of a sum-typed positioned formula. -/
structure InheritedCanonicalIncidenceRouteSuffixes
    {Source Auxiliary : Type*}
    (target : PositionedPeriodicCNF (Sum Source Auxiliary))
    (placement :
      PeriodicVariablePlacement (Sum Source Auxiliary))
    (splicePoint : Nat → Nat → Cell) where
  routes : IncidenceRoutes
  endpoints :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ target.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        ∀ sourceAtom,
          literal.atom = .inl sourceAtom →
          (routes clauseIndex literalIndex).head? =
              some (splicePoint clauseIndex literalIndex) ∧
            (routes clauseIndex literalIndex).getLast? =
              some
                (canonicalLiteralPosition
                  placement clause literal)
  orthogonal :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ target.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        ∀ sourceAtom,
          literal.atom = .inl sourceAtom →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex)

/-- Use the inherited suffix on source atoms and a singleton suffix on local
auxiliaries.  Invalid presentation indices receive the harmless empty route. -/
def completeSumIncidenceRouteSuffixesRoutes
    {Source Auxiliary : Type*}
    {target : PositionedPeriodicCNF (Sum Source Auxiliary)}
    {placement :
      PeriodicVariablePlacement (Sum Source Auxiliary)}
    {splicePoint : Nat → Nat → Cell}
    (inherited :
      InheritedCanonicalIncidenceRouteSuffixes
        target placement splicePoint) :
    IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match target.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            match literal.atom with
            | .inl _ =>
                inherited.routes clauseIndex literalIndex
            | .inr _ =>
                [splicePoint clauseIndex literalIndex]

/-- Trivial local auxiliary suffixes plus the supplied inherited suffixes
form a complete canonical suffix family. -/
def completeSumIncidenceRouteSuffixes
    {Source Auxiliary : Type*}
    (target : PositionedPeriodicCNF (Sum Source Auxiliary))
    (placement :
      PeriodicVariablePlacement (Sum Source Auxiliary))
    (splicePoint : Nat → Nat → Cell)
    (inherited :
      InheritedCanonicalIncidenceRouteSuffixes
        target placement splicePoint)
    (auxiliaryEndpoint :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ target.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          ∀ auxiliary,
            literal.atom = .inr auxiliary →
            splicePoint clauseIndex literalIndex =
              canonicalLiteralPosition
                placement clause literal) :
    CanonicalIncidenceRouteSuffixes
      target placement splicePoint where
  routes :=
    completeSumIncidenceRouteSuffixesRoutes inherited
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have clauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp clauseMember
    have literalLookup :=
      (List.mem_zipIdx_iff_getElem?).mp literalMember
    cases atomEquation : literal.atom with
    | inl sourceAtom =>
        simpa [completeSumIncidenceRouteSuffixesRoutes,
          clauseLookup, literalLookup, atomEquation] using
          inherited.endpoints
            clause clauseIndex clauseMember
            literal literalIndex literalMember
            sourceAtom atomEquation
    | inr auxiliary =>
        have endpointEqual :=
          auxiliaryEndpoint
            clause clauseIndex clauseMember
            literal literalIndex literalMember
            auxiliary atomEquation
        simp [completeSumIncidenceRouteSuffixesRoutes,
          clauseLookup, literalLookup, atomEquation,
          endpointEqual]
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have clauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp clauseMember
    have literalLookup :=
      (List.mem_zipIdx_iff_getElem?).mp literalMember
    cases atomEquation : literal.atom with
    | inl sourceAtom =>
        simpa [completeSumIncidenceRouteSuffixesRoutes,
          clauseLookup, literalLookup, atomEquation] using
          inherited.orthogonal
            clause clauseIndex clauseMember
            literal literalIndex literalMember
            sourceAtom atomEquation
    | inr auxiliary =>
        simp [completeSumIncidenceRouteSuffixesRoutes,
          clauseLookup, literalLookup, atomEquation,
          PeriodicOrthocrossing.OrthogonalPolyline]

end PositionedPeriodicCNF
end LeanTrominoes
