import ContinuousFlexibility.Analysis.SmoothDivisionBounds
import ContinuousFlexibility.Analysis.CanonicalCubicJets

/-!
# Mixed fixed-loss bounds for an actual simple radial factor

A genuine factorization F(r,θ)=r G(r,θ) identifies G with the first
Taylor integral. Every mixed derivative therefore loses exactly one
radial derivative of F, independently of the derivative order.
The bound applies on either side of the radial zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology Interval

set_option backward.isDefEq.respectTransparency false

/-- Joint smoothness and an actual radial factorization determine the
factor by the first Taylor integral, including its value at the zero. -/
theorem smoothRadialFactor_eq_integral {F G : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hfactor : ∀ q : PolarPoint, F q = q.1 * G q) (p : PolarPoint) :
    G p = ∫ t in (0 : ℝ)..1, mixedDerivative 1 0 F (t * p.1, p.2) := by
  have hFs : ContDiff ℝ ∞ (fun r : ℝ => F (r, p.2)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hGs : ContDiff ℝ ∞ (fun r : ℝ => G (r, p.2)) :=
    hG.comp (contDiff_id.prodMk contDiff_const)
  simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one] using
    smoothDivisionFactor_eq_integral hFs hGs (fun r => hfactor (r, p.2)) p.1

/-- The actual mixed derivative of the factor has a fixed loss of one. -/
theorem mixedDerivative_smoothRadialFactor_eq_integral {F G : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hfactor : ∀ q : PolarPoint, F q = q.1 * G q)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b G p =
      ∫ t in (0 : ℝ)..1, t ^ a * mixedDerivative (a + 1) b F (t * p.1, p.2) := by
  have he : G = fun q : PolarPoint =>
      ∫ t in (0 : ℝ)..1, (1 : ℝ) * mixedDerivative 1 0 F (t * q.1, q.2) := by
    funext q
    simpa only [one_mul] using smoothRadialFactor_eq_integral hF hG hfactor q
  rw [he, mixedDerivative_scaled_cylinderIntegral continuous_const
    (contDiff_mixedDerivative hF 1 0), mixedDerivative_radialJet hF a b 1]
  simp only [one_mul]

/-- No sign restriction on the radius is needed: the entire segment
from zero to the point is tested by the displayed hypothesis. -/
theorem abs_mixedDerivative_smoothRadialFactor_le {F G : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hfactor : ∀ q : PolarPoint, F q = q.1 * G q)
    (a b : ℕ) {p : PolarPoint} {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |mixedDerivative (a + 1) b F (t * p.1, p.2)| ≤ M) :
    |mixedDerivative a b G p| ≤ M := by
  have hM : 0 ≤ M :=
    (abs_nonneg _).trans (hbound 0 ⟨le_rfl, zero_le_one⟩)
  rw [mixedDerivative_smoothRadialFactor_eq_integral hF hG hfactor]
  have hpoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖t ^ a * mixedDerivative (a + 1) b F (t * p.1, p.2)‖ ≤ M := by
    have hpow0 : 0 ≤ t ^ a := pow_nonneg ht.1.le a
    have hpow1 : t ^ a ≤ 1 := pow_le_one₀ ht.1.le ht.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow0]
    calc
      _ ≤ t ^ a * M :=
        mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩) hpow0
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hpow1 hM
      _ = M := one_mul M
  have hint := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hpoint)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 1)
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const, sub_zero, one_smul] using hint

/-- The same positive half-width works for both signs and every angle. -/
theorem mul_radial_mem_symmetric_strip {R x t : ℝ}
    (hR : 0 < R) (hx : x ∈ Ioo (-R) R) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * x ∈ Ioo (-R) R := by
  have hxabs : |x| < R := abs_lt.mpr hx
  have htx : |t * x| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg ht.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (abs_nonneg x)
  exact abs_lt.mp (htx.trans_lt hxabs)

/-- Spatial one-high estimates for a numerator retain the same low
domain and the same constants, with exactly one added derivative loss.
All constants are selected before the state and the evaluation point. -/
theorem smoothRadialFactor_fixed_loss_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (U : Set E) (F G : E → PolarPoint → ℝ)
    (A : ℕ → ℝ) (loss : ℕ) {R : ℝ} (hR : 0 < R)
    (hF : ∀ z ∈ U, ContDiff ℝ ∞ (F z))
    (hG : ∀ z ∈ U, ContDiff ℝ ∞ (G z))
    (hfactor : ∀ z ∈ U, ∀ q : PolarPoint, F z q = q.1 * G z q)
    (hbound : ∀ s : ℕ, ∀ z ∈ U, ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        |mixedDerivative a b (F z) q| ≤ A s * (1 + p (s + loss) z)) :
    ∀ s : ℕ, ∀ z ∈ U, ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        |mixedDerivative a b (G z) q| ≤ A (s + 1) *
          (1 + p (s + (loss + 1)) z) := by
  intro s z hz a b hab q hq
  have hj := abs_mixedDerivative_smoothRadialFactor_le
    (hF z hz) (hG z hz) (hfactor z hz) a b
    (p := q) (M := A (s + 1) * (1 + p ((s + 1) + loss) z))
    (fun t ht => hbound (s + 1) z hz (a + 1) b (by omega)
      (t * q.1, q.2) ⟨mul_radial_mem_symmetric_strip hR hq.1 ht, mem_univ _⟩)
  simpa only [Nat.add_assoc, Nat.add_comm 1 loss] using hj

end ContinuousFlexibility.Analysis
