import LeanTrominoes.PeriodicThreeDMComputability
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificateComputability
import Mathlib.Computability.RE

/-!
# Exhaustive search for certified periodic 3DM drawings

The finite drawing verifier can be searched by enumerating the standard
`Primcodable` encoding of `PeriodicGridDrawing`.  This module isolates that
generic minimization argument: if a computable source map always admits a
verified drawing, then choosing the first verified drawing is a total
computable function.
-/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace FiniteDrawingSearch

/-- Harmless fallback used when a natural number does not decode as a
periodic grid drawing. -/
def defaultDrawing : PeriodicGridDrawing :=
  { gridSizePred := 0
    vertexPositions := []
    edgeRoutes := [] }

/-- The candidate drawing at one natural-number search index. -/
noncomputable def drawingAt (index : Nat) : PeriodicGridDrawing :=
  (Encodable.decode (α := PeriodicGridDrawing) index).getD defaultDrawing

@[simp]
theorem drawingAt_encode (drawing : PeriodicGridDrawing) :
    drawingAt (Encodable.encode drawing) = drawing := by
  simp [drawingAt]

theorem drawingAt_primrec : Primrec drawingAt := by
  exact
    (Primrec.option_getD.comp Primrec.decode
      (Primrec.const defaultDrawing)).of_eq fun _ => rfl

/-- A problem has at least one candidate accepted by the finite verifier. -/
def HasVerifiedDrawing (problem : PeriodicThreeDM) : Prop :=
  ∃ drawing, FiniteDrawingCertificate.verifies problem drawing = true

/-- Every verified drawing occurs in the natural-number candidate
enumeration. -/
theorem exists_verifiedAt_of_hasVerifiedDrawing
    {problem : PeriodicThreeDM}
    (available : HasVerifiedDrawing problem) :
    ∃ index,
      FiniteDrawingCertificate.verifies problem (drawingAt index) = true := by
  rcases available with ⟨drawing, checked⟩
  exact ⟨Encodable.encode drawing, by simpa using checked⟩

/-- The first natural-number index whose decoded drawing passes the finite
verifier. -/
noncomputable def firstVerifiedIndex (problem : PeriodicThreeDM)
    (available : HasVerifiedDrawing problem) : Nat :=
  Nat.find (exists_verifiedAt_of_hasVerifiedDrawing available)

theorem firstVerifiedIndex_spec (problem : PeriodicThreeDM)
    (available : HasVerifiedDrawing problem) :
    FiniteDrawingCertificate.verifies problem
      (drawingAt (firstVerifiedIndex problem available)) = true := by
  exact Nat.find_spec (exists_verifiedAt_of_hasVerifiedDrawing available)

theorem firstVerifiedIndex_minimal (problem : PeriodicThreeDM)
    (available : HasVerifiedDrawing problem) {index : Nat}
    (checked :
      FiniteDrawingCertificate.verifies problem (drawingAt index) = true) :
    firstVerifiedIndex problem available ≤ index := by
  exact Nat.find_min' (exists_verifiedAt_of_hasVerifiedDrawing available) checked

/-- The first verified drawing in the standard encoding. -/
noncomputable def firstVerifiedDrawing (problem : PeriodicThreeDM)
    (available : HasVerifiedDrawing problem) : PeriodicGridDrawing :=
  drawingAt (firstVerifiedIndex problem available)

theorem firstVerifiedDrawing_spec (problem : PeriodicThreeDM)
    (available : HasVerifiedDrawing problem) :
    FiniteDrawingCertificate.verifies problem
      (firstVerifiedDrawing problem available) = true := by
  exact firstVerifiedIndex_spec problem available

/-- Run exhaustive verified-drawing search after an arbitrary source map. -/
noncomputable def searchIndex {Input : Type*}
    (problemOf : Input → PeriodicThreeDM)
    (available : ∀ input, HasVerifiedDrawing (problemOf input))
    (input : Input) : Nat :=
  firstVerifiedIndex (problemOf input) (available input)

/-- Decode the candidate selected by `searchIndex`. -/
noncomputable def searchDrawing {Input : Type*}
    (problemOf : Input → PeriodicThreeDM)
    (available : ∀ input, HasVerifiedDrawing (problemOf input))
    (input : Input) : PeriodicGridDrawing :=
  drawingAt (searchIndex problemOf available input)

theorem searchDrawing_spec {Input : Type*}
    (problemOf : Input → PeriodicThreeDM)
    (available : ∀ input, HasVerifiedDrawing (problemOf input))
    (input : Input) :
    FiniteDrawingCertificate.verifies (problemOf input)
      (searchDrawing problemOf available input) = true := by
  exact firstVerifiedDrawing_spec (problemOf input) (available input)

/-- Reconstruct the proof-carrying continuously planar presentation from the
drawing selected by exhaustive search. -/
noncomputable def searchCertifiedPresentation {Input : Type*}
    (problemOf : Input → PeriodicThreeDM)
    (wellFormed : ∀ input, (problemOf input).IsWellFormed)
    (available : ∀ input, HasVerifiedDrawing (problemOf input))
    (input : Input) :
    FiniteDrawingCertificate.CertifiedPresentation (problemOf input) :=
  FiniteDrawingCertificate.certifiedPresentationOfVerified
    (wellFormed input) (searchDrawing_spec problemOf available input)

/-- The predicate searched by `searchIndex` is computable for every
computable source problem. -/
theorem verifiedCandidate_computable {Input : Type*} [Primcodable Input]
    {problemOf : Input → PeriodicThreeDM}
    (problemOfComputable : Computable problemOf) :
    ComputablePred fun input : Input × Nat =>
      FiniteDrawingCertificate.verifies
        (problemOf input.1) (drawingAt input.2) = true := by
  have checkComputable : Computable fun input : Input × Nat =>
      FiniteDrawingCertificate.verifies
        (problemOf input.1) (drawingAt input.2) :=
    FiniteDrawingCertificate.verifies_computable.comp
      (problemOfComputable.comp Computable.fst)
      (drawingAt_primrec.to_comp.comp Computable.snd)
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun input : Input × Nat =>
      FiniteDrawingCertificate.verifies
        (problemOf input.1) (drawingAt input.2), checkComputable, ?_⟩
  funext input
  apply propext
  simp

/-- Total unbounded search for the first certificate is computable whenever
the searched source family always has a certificate. -/
theorem searchIndex_computable {Input : Type*} [Primcodable Input]
    {problemOf : Input → PeriodicThreeDM}
    (problemOfComputable : Computable problemOf)
    (available : ∀ input, HasVerifiedDrawing (problemOf input)) :
    Computable (searchIndex problemOf available) := by
  have found := Computable.find
    (P := fun input index =>
      FiniteDrawingCertificate.verifies
        (problemOf input) (drawingAt index) = true)
    (verifiedCandidate_computable problemOfComputable)
    (fun input =>
      exists_verifiedAt_of_hasVerifiedDrawing (available input))
  apply found.of_eq
  intro input
  unfold searchIndex firstVerifiedIndex
  congr

/-- The drawing returned by total unbounded certificate search is itself a
computable function of the source input. -/
theorem searchDrawing_computable {Input : Type*} [Primcodable Input]
    {problemOf : Input → PeriodicThreeDM}
    (problemOfComputable : Computable problemOf)
    (available : ∀ input, HasVerifiedDrawing (problemOf input)) :
    Computable (searchDrawing problemOf available) := by
  exact drawingAt_primrec.to_comp.comp
    (searchIndex_computable problemOfComputable available)

end FiniteDrawingSearch
end PeriodicThreeDM
end LeanTrominoes
