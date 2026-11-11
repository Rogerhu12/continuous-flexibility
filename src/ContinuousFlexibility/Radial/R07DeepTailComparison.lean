import ContinuousFlexibility.Radial.R07DeepTailChainIntegrals
import ContinuousFlexibility.Radial.R07DeepTailRawBounds

/-!
# Comparing every physical frequency with the normalized frequency two

Once a fixed frequency's entrance is sufficiently near the endpoint,
all mass and resistance integrals differ from their frequency-two values
by factors between `exp (-1)` and `exp 1`. This includes the complete
initial resistance interval at the left endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def R07UnitCompare (a b : ℝ) : Prop := exp (-1) * b ≤ a ∧ a ≤ exp 1 * b

theorem r07_unitCompare_mul {a b c d : ℝ} (hab : R07UnitCompare a b)
    (hcd : R07UnitCompare c d) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    exp (-2) * (b * d) ≤ a * c ∧ a * c ≤ exp 2 * (b * d) := by
  have ha : 0 ≤ a := (mul_nonneg (exp_pos _).le hb).trans hab.1
  have hc : 0 ≤ c := (mul_nonneg (exp_pos _).le hd).trans hcd.1
  have hlo := mul_le_mul hab.1 hcd.1 (mul_nonneg (exp_pos _).le hd) ha
  have hhi := mul_le_mul hab.2 hcd.2 hc (mul_nonneg (exp_pos _).le hb)
  have heNeg : exp (-1 : ℝ) * exp (-1) = exp (-2) := by rw [← exp_add]; norm_num
  have hePos : exp (1 : ℝ) * exp 1 = exp 2 := by rw [← exp_add]; norm_num
  constructor
  · calc
      _ = (exp (-1) * b) * (exp (-1) * d) := by rw [← heNeg]; ring
      _ ≤ _ := hlo
  · calc
      _ ≤ (exp 1 * b) * (exp 1 * d) := hhi
      _ = _ := by rw [← hePos]; ring

theorem r07_unitCompare_domination {a b c d L : ℝ}
    (hab : R07UnitCompare a b) (hcd : R07UnitCompare c d)
    (hL : 0 ≤ L) (hbd : b ≤ L * d) : a ≤ (exp 2 * L) * c := by
  have he : exp (1 : ℝ) * exp (-1) = 1 := by rw [← exp_add]; norm_num
  have hd : d ≤ exp 1 * c := by
    calc
      _ = exp 1 * (exp (-1) * d) := by rw [← mul_assoc, he, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcd.1 (exp_pos _).le
  calc
    _ ≤ exp 1 * b := hab.2
    _ ≤ exp 1 * (L * d) := mul_le_mul_of_nonneg_left hbd (exp_pos _).le
    _ ≤ exp 1 * (L * (exp 1 * c)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hL) (exp_pos _).le
    _ = _ := by
      have htwo : exp (1 : ℝ) * exp 1 = exp 2 := by rw [← exp_add]; norm_num
      rw [← htwo]
      ring

theorem r07_normalized_unitCompare_mul {a b c d s : ℝ} (hs : 0 < s)
    (hab : R07UnitCompare a (s⁻¹ * b)) (hcd : R07UnitCompare c (s * d))
    (hb : 0 ≤ b) (hd : 0 ≤ d) :
    exp (-2) * (b * d) ≤ a * c ∧ a * c ≤ exp 2 * (b * d) := by
  have h := r07_unitCompare_mul hab hcd (by positivity) (by positivity)
  have he : (s⁻¹ * b) * (s * d) = b * d := by field_simp [hs.ne']
  simpa only [he] using h

theorem r07_log_radius_ratio_abs (right : Bool) {e : ℝ} (he : 0 < e) (x : ℝ) :
    |log (tailPhysicalRadius right x / e)| = |x - r07OutwardLog right e| := by
  rw [log_div (r07_radius_pos right x).ne' he.ne']
  cases right
  · simp only [tailPhysicalRadius, r07OutwardLog, Bool.false_eq_true, if_false, log_exp]
    rw [show -x - log e = -(x - -log e) by ring, abs_neg]
  · simp only [tailPhysicalRadius, r07OutwardLog, if_true, log_exp]

theorem r07_physical_compare_near_endpoint {D : ReferenceData} {right : Bool}
    {j : ℕ} {entrance a b : ℝ} (hD : RadialProfileGeometry D) (hj : 2 ≤ j)
    (he : tailPhysicalRadius right entrance ∈ radialCore D)
    (hclose : r07OutwardLog right (if right then D.b else D.a) - entrance ≤
      (2 * (j : ℝ) ^ 2)⁻¹)
    (hea : entrance ≤ a) (hab : a ≤ b)
    (hbe : b < r07OutwardLog right (if right then D.b else D.a)) :
    R07UnitCompare (∫ x in a..b, r07PhysicalDensity D right j x)
        (∫ x in a..b, r07PhysicalDensity D right 2 x) ∧
      R07UnitCompare (∫ x in a..b, (r07PhysicalDensity D right j x)⁻¹)
        (∫ x in a..b, (r07PhysicalDensity D right 2 x)⁻¹) := by
  have hep : 0 < (if right then D.b else D.a) := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hj0 : 2 * (j : ℝ) ^ 2 ≠ 0 := (mul_pos (by norm_num) (pow_pos hjp 2)).ne'
  have hprod : (2 * (j : ℝ) ^ 2) * (2 * (j : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hj0
  have hc := r07_physical_mass_resistance_comparison hj hab hep hD.2.2.1.1
    (fun x hx => hD.2.2.2.2.1 _ (r07_physical_radius_core_of_Ico hD he
      ⟨hea.trans hx.1, hx.2.trans_lt hbe⟩))
    (L := (2 * (j : ℝ) ^ 2)⁻¹) (fun x hx => by
      rw [r07_log_radius_ratio_abs right hep,
        abs_of_nonpos (sub_nonpos.mpr (hx.2.trans hbe.le))]
      linarith only [hclose, hea, hx.1])
  simpa only [R07UnitCompare, hprod] using hc

theorem r07_deepTail_node_bounds {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) (n : ℕ) :
    let Q := r07DeepTailData T D right j start η K
    Q.entrance ≤ Q.node n ∧ Q.node n < Q.endpoint ∧ Q.massEnd n < Q.endpoint := by
  let Q := r07DeepTailData T D right j start η K
  have hn : T.index ≤ start + n := hstart.le.trans (Nat.le_add_right start n)
  have hmono : Monotone Q.node := monotone_nat_of_le_succ (fun k =>
    ((r07_deepTail_interval_order h right j hstart η K k).1.trans
      (r07_deepTail_interval_order h right j hstart η K k).2).le)
  have hzero : Q.entrance ≤ Q.node 0 := by
    have hi := r07_deepTail_initial_order h right j hstart η K
    cases right
    · exact hi.le
    · exact hi.le
  have hc := r07_chain_mass_nodes_core h right hn
  exact ⟨hzero.trans (hmono (Nat.zero_le n)),
    r07_outwardLog_lt_endpoint (r07_realization_geometry h) right hc.1,
    r07_outwardLog_lt_endpoint (r07_realization_geometry h) right hc.2⟩

theorem r07_deepTail_integrals_compare {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {j start : ℕ} (hj : 2 ≤ j) (hstart : T.index < start) (η K : ℝ)
    (hclose : (r07DeepTailData T D right j start η K).endpoint -
      (r07DeepTailData T D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) (n : ℕ) :
    let Q := r07DeepTailData T D right j start η K
    let s := (if right then D.b else D.a) ^ 8
    R07UnitCompare (tailMass Q n) (s⁻¹ * morseCellMass T D right (start + n)) ∧
      R07UnitCompare (tailInnerResistance Q n) (s * morseCellResistance T D right (start + n)) ∧
      R07UnitCompare (tailGapMass Q n) (s⁻¹ * morseJoinMass T D right (r07GapIndex right (start + n))) ∧
      R07UnitCompare (tailResistance Q n) (s * morseJoinResistance T D right (r07GapIndex right (start + n))) := by
  let Q := r07DeepTailData T D right j start η K
  have ho := r07_deepTail_interval_order h right j hstart η K n
  have hb := r07_deepTail_node_bounds h right j hstart η K n
  have hbn := r07_deepTail_node_bounds h right j hstart η K (n + 1)
  have hc := r07_physical_compare_near_endpoint (r07_realization_geometry h) hj
    (r07_deepTail_entrance_core h right j hstart η K) hclose hb.1 ho.1.le hb.2.2
  have hg := r07_physical_compare_near_endpoint (r07_realization_geometry h) hj
    (r07_deepTail_entrance_core h right j hstart η K) hclose
    (hb.1.trans ho.1.le) ho.2.le hbn.2.1
  have hcell := r07_deepTail_cell_integrals h right hstart.le η K n
  have hgap := r07_deepTail_gap_integrals h right hstart.le η K n
  change R07UnitCompare (tailMass Q n)
      (tailMass (r07DeepTailData T D right 2 start η K) n) ∧
    R07UnitCompare (tailInnerResistance Q n)
      (tailInnerResistance (r07DeepTailData T D right 2 start η K) n) at hc
  change R07UnitCompare (tailGapMass Q n)
      (tailGapMass (r07DeepTailData T D right 2 start η K) n) ∧
    R07UnitCompare (tailResistance Q n)
      (tailResistance (r07DeepTailData T D right 2 start η K) n) at hg
  rw [hcell.1, hcell.2] at hc
  rw [hgap.1, hgap.2] at hg
  exact ⟨hc.1, hc.2, hg.1, hg.2⟩

theorem r07_deepTail_initial_compare {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {j start : ℕ} (hj : 2 ≤ j) (hstart : T.index < start) (η K : ℝ)
    (hclose : (r07DeepTailData T D right j start η K).endpoint -
      (r07DeepTailData T D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) :
    let Q := r07DeepTailData T D right j start η K
    let s := (if right then D.b else D.a) ^ 8
    R07UnitCompare (tailInitialGapMass Q)
        (if right then 0 else s⁻¹ * morseJoinMass T D right start) ∧
      R07UnitCompare (tailInitialResistance Q)
        (if right then 0 else s * morseJoinResistance T D right start) := by
  have hb := r07_deepTail_node_bounds h right j hstart η K 0
  have hc := r07_physical_compare_near_endpoint (r07_realization_geometry h) hj
    (r07_deepTail_entrance_core h right j hstart η K) hclose le_rfl hb.1 hb.2.1
  have hi := r07_deepTail_initial_integrals h right hstart η K
  change R07UnitCompare (tailInitialGapMass (r07DeepTailData T D right j start η K))
      (tailInitialGapMass (r07DeepTailData T D right 2 start η K)) ∧
    R07UnitCompare (tailInitialResistance (r07DeepTailData T D right j start η K))
      (tailInitialResistance (r07DeepTailData T D right 2 start η K)) at hc
  rw [hi.1, hi.2] at hc
  exact hc

end ContinuousFlexibility.Radial
