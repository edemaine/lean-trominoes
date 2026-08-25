/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorNatSemantics

/-! # Natural-prefix skipping for signed carrier-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem scan_routeNatField_to_segment_unselected
    (field : Field) (unselected : selectsNat field .route = false)
    (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition field) (.nat .route)
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      FiniteStateTransducer.scan (transition field) (.nat .segment)
        (suffix.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [FiniteStateTransducer.scan_append,
    scan_natUnits_unselected field .route unselected]
  simp [FiniteStateTransducer.scan, transition, unselected]

theorem scan_segmentNatField_to_horizontalSign
    (field : Field) (unselected : selectsNat field .segment = false)
    (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition field) (.nat .segment)
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      FiniteStateTransducer.scan (transition field) (.intSign .horizontal)
        (suffix.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [FiniteStateTransducer.scan_append,
    scan_natUnits_unselected field .segment unselected]
  simp [FiniteStateTransducer.scan, transition, unselected]

theorem scan_natPrefix_to_horizontalSign
    (field : Field)
    (routeUnselected : selectsNat field .route = false)
    (segmentUnselected : selectsNat field .segment = false)
    (routeIndex segmentIndex : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition field) (.nat .route)
        ((CarrierKeyWords.natField routeIndex ++
            CarrierKeyWords.natField segmentIndex ++ suffix).map
          DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      FiniteStateTransducer.scan (transition field) (.intSign .horizontal)
        (suffix.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) := by
  calc
    _ = FiniteStateTransducer.scan (transition field) (.nat .segment)
        ((CarrierKeyWords.natField segmentIndex ++ suffix).map
          DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) := by
      simpa only [List.append_assoc] using
        scan_routeNatField_to_segment_unselected field routeUnselected
          routeIndex (CarrierKeyWords.natField segmentIndex ++ suffix)
    _ = _ :=
      scan_segmentNatField_to_horizontalSign field segmentUnselected
        segmentIndex suffix

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
