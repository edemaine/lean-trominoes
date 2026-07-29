import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeMembership
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicization
import LeanTrominoes.PeriodicCNFPlanarPeriodicCompleteness

/-!
# Periodic soundness of retained carrier links

The retained finite formula contains only one owned representative of each
periodic straight-carrier equality.  This file transfers that finite equality
back to every raw neighboring physical link.  The key bookkeeping fact is
that translating a physical carrier node is equivalent to translating the
finite assignment at which its normalized periodic variable is evaluated.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Evaluating a translated physical carrier node at one finite-block
translate is the same as evaluating the original node at the sum of the two
translations. -/
theorem planarSATFiniteAssignmentAt_carrier_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (translate shift : Cell) (node : CarrierNode) :
    planarSATFiniteAssignmentAt formula assignment translate
        (.inl (.carrier
          (node.periodTranslate
            (PeriodicCNF.incidenceGraph formula) shift))) =
      planarSATFiniteAssignmentAt formula assignment
        (Cell.add translate shift) (.inl (.carrier node)) := by
  let graph := PeriodicCNF.incidenceGraph formula
  have normalized :
      normalizePlanarSATVariable formula
          (.inl (.carrier (node.periodTranslate graph shift))) =
        (periodicCarrierNodeToPlanarSATVariable
            (normalizeCarrierNode graph node).1,
          Cell.add (normalizeCarrierNode graph node).2 shift) := by
    have translated :=
      normalizeCarrierNode_periodTranslate graph node shift
    cases node <;>
      simpa [graph, normalizePlanarSATVariable,
        periodicCarrierNodeToPlanarSATVariable] using translated
  have original :
      normalizePlanarSATVariable formula (.inl (.carrier node)) =
        (periodicCarrierNodeToPlanarSATVariable
            (normalizeCarrierNode graph node).1,
          (normalizeCarrierNode graph node).2) := by
    cases node <;> rfl
  unfold planarSATFiniteAssignmentAt
  rw [normalized, original, Cell.add_assoc]

/-- A satisfying retained periodic formula enforces the equality belonging
to every raw retained link whose first endpoint lies in the neighboring
source window, even when that physical link is not itself the selected
finite representative. -/
theorem retainedDrawingCompleteCarrierLink_assignment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (translate : Cell)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw
        (PeriodicCNF.incidenceGraph formula))
    (sourceNeighbor :
      IsNeighborTranslation link.first.translate) :
    planarSATFiniteAssignmentAt formula assignment translate
        (.inl (.carrier link.first)) =
      planarSATFiniteAssignmentAt formula assignment translate
        (.inl (.carrier link.second)) := by
  let graph := PeriodicCNF.incidenceGraph formula
  let correction :=
    carrierLinkRepresentativeCorrection graph link
  let representative :=
    carrierLinkPeriodTranslate graph link correction
  have representativeMem :
      representative ∈ retainedDrawingCompleteCarrierLinks graph := by
    exact
      retainedDrawingCompleteCarrierLink_representativeCorrection_mem
        wellFormed degree isLocal linkMem sourceNeighbor
  let representativeTranslate := Cell.sub translate correction
  let finiteAssignment :=
    planarSATFiniteAssignmentAt formula assignment
      representativeTranslate
  have finiteHolds :
      FormulaHolds finiteAssignment
        (retainedDrawingPlanarSATFormula formula) := by
    exact
      (retainedDrawingPeriodicPlanarSATFormula_satisfies_iff
        formula assignment).mp satisfies representativeTranslate
  have coreHolds :
      FormulaHolds
          (finiteAssignment ∘ planarSATCoreVariableMap)
          (retainedDrawingRoutePlanarCoreFormula graph) :=
    (retainedDrawingPlanarSATFormula_holds_iff
      formula finiteAssignment).mp finiteHolds |>.1
  have wireHolds :
      FormulaHolds
          ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
          (retainedDrawingRouteWireFormula graph) :=
    (retainedDrawingRoutePlanarCoreFormula_holds_iff
      graph (finiteAssignment ∘ planarSATCoreVariableMap)).mp
        coreHolds |>.2
  have carrierHolds :
      FormulaHolds
          ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
          (retainedDrawingCompleteCarrierFormula graph) := by
    exact
      (formulaHolds_route_append_iff
        ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
        (retainedDrawingCompleteCarrierFormula graph)
        (drawingRouteBendFormula graph)).mp
          (by simpa [retainedDrawingRouteWireFormula] using wireHolds) |>.1
  have representativeEq :
      finiteAssignment (.inl (.carrier representative.first)) =
        finiteAssignment (.inl (.carrier representative.second)) := by
    have laws :=
      (equalityFamily_holds_iff
        (((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl))
        (retainedDrawingCompleteCarrierLinks graph)).mp
          (by
            simpa [retainedDrawingCompleteCarrierFormula] using
              carrierHolds)
    simpa [Function.comp_def, planarSATCoreVariableMap] using
      laws representative representativeMem
  have translateBack :
      Cell.add representativeTranslate correction = translate := by
    rcases translate with ⟨translateX, translateY⟩
    rcases correction with ⟨correctionX, correctionY⟩
    simp [representativeTranslate, Cell.add, Cell.sub]
  have firstBack :
      finiteAssignment (.inl (.carrier representative.first)) =
        planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier link.first)) := by
    change
      planarSATFiniteAssignmentAt formula assignment
          representativeTranslate
          (.inl (.carrier
            (link.first.periodTranslate graph correction))) =
        _
    rw [planarSATFiniteAssignmentAt_carrier_periodTranslate,
      translateBack]
  have secondBack :
      finiteAssignment (.inl (.carrier representative.second)) =
        planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier link.second)) := by
    change
      planarSATFiniteAssignmentAt formula assignment
          representativeTranslate
          (.inl (.carrier
            (link.second.periodTranslate graph correction))) =
        _
    rw [planarSATFiniteAssignmentAt_carrier_periodTranslate,
      translateBack]
  exact firstBack.symm.trans (representativeEq.trans secondBack)

end PeriodicOrthocrossing
end LeanTrominoes
