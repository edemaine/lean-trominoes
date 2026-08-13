import LeanTrominoes.EncodingBounds
import LeanTrominoes.PeriodicStripFlatEncoding

/-!
# Input-size bounds for the flat periodic-strip encoding

These are the representation-level estimates needed to port the verified
Savitch membership algorithm from the legacy recursively paired strip input
to the flat target encoding.
-/

namespace LeanTrominoes

namespace PeriodicStripFlatEncoding

private theorem length_le_fieldCostSum (fields : List Nat) :
    fields.length ≤
      (fields.map fun field =>
        (_root_.Computability.encodeNat field).length + 1).sum := by
  induction fields with
  | nil => simp
  | cons field fields ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

private theorem fieldCost_le_sum_of_mem (fields : List Nat) {field : Nat}
    (member : field ∈ fields) :
    (_root_.Computability.encodeNat field).length + 1 ≤
      (fields.map fun value =>
        (_root_.Computability.encodeNat value).length + 1).sum := by
  induction fields with
  | nil => simp at member
  | cons head fields ih =>
      simp only [List.mem_cons] at member
      simp only [List.map_cons, List.sum_cons]
      rcases member with rfl | member
      · omega
      · have tail := ih member
        omega

/-- The number of natural fields is at most the number of flat input symbols. -/
theorem stripFields_length_le_encoding_length
    (periodicStrip : PeriodicStrip) :
    (stripFields periodicStrip).length ≤
      (finEncoding.encode periodicStrip).length := by
  rw [finEncoding_encode_length]
  exact length_le_fieldCostSum _

/-- Every individual natural field contributes its own binary digits and
delimiter to the complete input. -/
theorem field_encodeNat_length_add_one_le_encoding_length
    (periodicStrip : PeriodicStrip) {field : Nat}
    (member : field ∈ stripFields periodicStrip) :
    (_root_.Computability.encodeNat field).length + 1 ≤
      (finEncoding.encode periodicStrip).length := by
  rw [finEncoding_encode_length]
  exact fieldCost_le_sum_of_mem _ member

/-- The explicit motif length is linearly bounded by the flat input length. -/
theorem motif_length_le_encoding_length (periodicStrip : PeriodicStrip) :
    periodicStrip.motif.length ≤
      (finEncoding.encode periodicStrip).length := by
  have fields := stripFields_length_le_encoding_length periodicStrip
  rw [stripFields_length] at fields
  omega

/-- The period's ordinary binary representation occurs verbatim as the second
flat input field. -/
theorem period_encodeNat_length_le_encoding_length
    (periodicStrip : PeriodicStrip) :
    (_root_.Computability.encodeNat periodicStrip.period).length ≤
      (finEncoding.encode periodicStrip).length := by
  have field := field_encodeNat_length_add_one_le_encoding_length
    periodicStrip (field := periodicStrip.period) (by
      simp [stripFields])
  omega

/-- The binary logarithm of the horizontal period is bounded by flat input
length. -/
theorem clog_period_le_encoding_length (periodicStrip : PeriodicStrip) :
    Nat.clog 2 periodicStrip.period ≤
      (finEncoding.encode periodicStrip).length := by
  apply Nat.le_trans (Nat.clog_le_of_le_pow ?_)
    (period_encodeNat_length_le_encoding_length periodicStrip)
  exact (EncodingBounds.nat_lt_pow_encodeNat_length
    periodicStrip.period).le

end PeriodicStripFlatEncoding

namespace PeriodicStrip.WindowState

/-- The existing sparse-frontier state space still needs only linear Savitch
depth when input size is measured in the new flat encoding. -/
theorem savitchDepth_le_flat_encoding_length (periodicStrip : PeriodicStrip) :
    FiniteState.savitchDepth (WindowState periodicStrip) ≤
      21 * (PeriodicStripFlatEncoding.finEncoding.encode
        periodicStrip).length + 1 := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  calc
    FiniteState.savitchDepth (WindowState periodicStrip) ≤
        Nat.clog 2 periodicStrip.period +
          20 * periodicStrip.motif.toFinset.card + 1 :=
      savitchDepth_windowState_le periodicStrip
    _ ≤ inputLength + 20 * periodicStrip.motif.length + 1 := by
      have periodBound :=
        PeriodicStripFlatEncoding.clog_period_le_encoding_length periodicStrip
      have motifCardBound := periodicStrip.motif.toFinset_card_le
      dsimp only [inputLength] at periodBound ⊢
      omega
    _ ≤ inputLength + 20 * inputLength + 1 := by
      have motifBound :=
        PeriodicStripFlatEncoding.motif_length_le_encoding_length periodicStrip
      dsimp only [inputLength] at motifBound ⊢
      omega
    _ = 21 * inputLength + 1 := by omega

end PeriodicStrip.WindowState

end LeanTrominoes
