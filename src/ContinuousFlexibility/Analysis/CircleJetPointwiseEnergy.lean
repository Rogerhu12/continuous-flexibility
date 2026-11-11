import ContinuousFlexibility.Analysis.CircleSobolevPointwise
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Finite component energies and composition of actual angular jets

A weighted point value uses only the two adjacent angular jets in the same
component.  The full component energy controls both, while preserving the
sample-weight exponent.  The ordinary higher chain rule therefore gives a
composition estimate before summing over the infinitely many circles.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The summand at one circle in the existing complete circle energy. -/
def circleComponentEnergy (T : MaterialData) (γ : ℝ) (s : ℕ)
    (u : ℕ → ℝ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∑ j : CircleJetIndex s,
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2

theorem circleComponentEnergy_lt_top
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (s m : ℕ) :
    circleComponentEnergy T γ s u m < ⊤ := by
  have h := ENNReal.le_tsum (f := circleComponentEnergy T γ s u) m
  exact h.trans_lt (hu.2.2 s)

/-- Every actual weighted L² jet is bounded by the square root of its
component's complete energy. -/
theorem circleWeightedL2_le_componentEnergy
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) {m a b s : ℕ}
    (hM : 0 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m))
    (horder : a + b ≤ s) :
    (T.M (T.sample m) ^ b * T.H (T.sample m) ^ (-γ)) *
      (eLpNorm (iteratedDeriv a (u m)) 2 angleMeasure).toReal ≤
        Real.sqrt (circleComponentEnergy T γ s u m).toReal := by
  let j : CircleJetIndex s :=
    ⟨fun i => if i = 0 then ⟨a, by omega⟩ else ⟨b, by omega⟩, by simpa using horder⟩
  let term (k : CircleJetIndex s) : ℝ≥0∞ :=
    ENNReal.ofReal ((T.M (T.sample m) ^ (k.val 1).val *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (k.val 0).val (u m)) 2 angleMeasure ^ 2
  have hsingle : term j ≤ circleComponentEnergy T γ s u m :=
    Finset.single_le_sum (f := term) (fun _ _ => zero_le) (Finset.mem_univ j)
  have hterm : ENNReal.ofReal
      ((T.M (T.sample m) ^ b * T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv a (u m)) 2 angleMeasure ^ 2 ≤
        circleComponentEnergy T γ s u m := by
    simpa [term, j] using hsingle
  have hreal := ENNReal.toReal_mono (circleComponentEnergy_lt_top hu s m).ne hterm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_pow] at hreal
  have hsq : ((T.M (T.sample m) ^ b * T.H (T.sample m) ^ (-γ)) *
      (eLpNorm (iteratedDeriv a (u m)) 2 angleMeasure).toReal) ^ 2 ≤
        (circleComponentEnergy T γ s u m).toReal := by
    simpa only [mul_pow] using hreal
  have hw : 0 ≤ T.M (T.sample m) ^ b * T.H (T.sample m) ^ (-γ) :=
    mul_nonneg (pow_nonneg hM b) (Real.rpow_nonneg hH _)
  have h := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq (mul_nonneg hw ENNReal.toReal_nonneg)] using h

/-- Weighted point evaluation needs one additional angular derivative and
retains exactly the original sample-weight power. -/
theorem circleWeighted_abs_le_componentEnergy
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) {m a b s : ℕ}
    (hM : 0 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m))
    (horder : a + b + 1 ≤ s) (θ : ℝ) :
    (T.M (T.sample m) ^ b * T.H (T.sample m) ^ (-γ)) *
      |iteratedDeriv a (u m) θ| ≤
        2 * circleSobolevConstant * Real.sqrt (circleComponentEnergy T γ s u m).toReal := by
  let w : ℝ := T.M (T.sample m) ^ b * T.H (T.sample m) ^ (-γ)
  have hw : 0 ≤ w := mul_nonneg (pow_nonneg hM b) (Real.rpow_nonneg hH _)
  have ha := circleWeightedL2_le_componentEnergy hu hM hH
    (a := a) (b := b) (s := s) (by omega)
  have ha1 := circleWeightedL2_le_componentEnergy hu hM hH
    (a := a + 1) (b := b) (s := s) (by omega)
  calc
    w * |iteratedDeriv a (u m) θ| ≤ w * (circleSobolevConstant *
        ((eLpNorm (iteratedDeriv a (u m)) 2 angleMeasure).toReal +
          (eLpNorm (iteratedDeriv (a + 1) (u m)) 2 angleMeasure).toReal)) :=
      mul_le_mul_of_nonneg_left
        (abs_periodic_iteratedDeriv_le_angleL2 (hu.1 m).1 (hu.1 m).2 a θ) hw
    _ = circleSobolevConstant *
        (w * (eLpNorm (iteratedDeriv a (u m)) 2 angleMeasure).toReal +
          w * (eLpNorm (iteratedDeriv (a + 1) (u m)) 2 angleMeasure).toReal) := by ring
    _ ≤ circleSobolevConstant *
        (Real.sqrt (circleComponentEnergy T γ s u m).toReal +
          Real.sqrt (circleComponentEnergy T γ s u m).toReal) :=
      mul_le_mul_of_nonneg_left (add_le_add ha ha1) circleSobolevConstant_nonneg
    _ = _ := by ring

/-- The actual higher chain rule with the weighted component energy of the
outer circle field.  There is one angular-order loss. -/
theorem circleWeighted_comp_iteratedDeriv_abs_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) {m n k s : ℕ}
    (hM : 0 < T.M (T.sample m)) (hH : 0 < T.H (T.sample m))
    (horder : n + k + 1 ≤ s) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (θ : ℝ) {B : ℝ}
    (hB : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i φ θ| ≤ B ^ i) :
    (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
      |iteratedDeriv n (u m ∘ φ) θ| ≤
        (2 * (n.factorial : ℝ) * circleSobolevConstant * B ^ n) *
          Real.sqrt (circleComponentEnergy T γ s u m).toReal := by
  let w : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  let E : ℝ := Real.sqrt (circleComponentEnergy T γ s u m).toReal
  have hw : 0 < w := mul_pos (pow_pos hM k) (Real.rpow_pos_of_pos hH _)
  have hout (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (u m) (φ θ)‖ ≤ (2 * circleSobolevConstant * E) / w := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, le_div_iff₀ hw]
    have h := circleWeighted_abs_le_componentEnergy hu hM.le hH.le
      (a := i) (b := k) (s := s) (by omega) (φ θ)
    simpa only [E, w, mul_comm _ w] using h
  have hin (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i φ θ‖ ≤ B ^ i := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hB i hi hin
  have hcomp := norm_iteratedFDeriv_comp_le (hu.1 m).1 hφ (n := n) (by simp) θ hout hin
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hcomp
  calc
    w * |iteratedDeriv n (u m ∘ φ) θ| ≤
        w * ((n.factorial : ℝ) * ((2 * circleSobolevConstant * E) / w) * B ^ n) :=
      mul_le_mul_of_nonneg_left hcomp hw.le
    _ = (2 * (n.factorial : ℝ) * circleSobolevConstant * B ^ n) * E := by
      field_simp [hw.ne']
      <;> ring

end ContinuousFlexibility.Statements
