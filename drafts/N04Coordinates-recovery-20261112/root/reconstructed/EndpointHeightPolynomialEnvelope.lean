import ContinuousFlexibility.Analysis.EndpointTaylorPolynomialEnvelope
import ContinuousFlexibility.Analysis.ExpPolynomialEnvelope
import ContinuousFlexibility.Analysis.EndpointHeightValueBounds

/-!
# Full jets of the actual positive height and its reciprocal

The zeroth-order amplitude is obtained from the true endpoint values and
the actual small-collar condition. The exponential chain rule then uses
only positive-order jets of the constructed exponent. In particular no
exponential of a high-jet envelope occurs in the bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

theorem exists_positiveHeightTaylorInterpolation_polynomial_envelope (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M H M₀ δ : ℝ},
      1 ≤ M → 1 ≤ H → H ≤ M → 0 ≤ M₀ → 0 < δ → δ ≤ 1 → δ⁻¹ ≤ M →
      ∀ (l r : ℝ) (q : Bool → PolarPoint → ℝ),
      (∀ side j, j ≤ n →
        ContDiff ℝ ∞ (positiveHeightTaylorData l r (fun _ => 1) q side j)) →
      (∀ side j, j ≤ n → ∀ b, b ≤ N → ∀ θ,
        |iteratedDeriv b (positiveHeightTaylorData l r (fun _ => 1) q side j) θ| ≤ M) →
      (∀ side θ, 0 < q side (if side then r else l, θ)) →
      (∀ side θ, q side (if side then r else l, θ) ≤ H) →
      (∀ side θ, (q side (if side then r else l, θ))⁻¹ ≤ H) →
      (∀ side j, 0 < j → j ≤ n → ∀ θ,
        |positiveHeightTaylorData l r (fun _ => 1) q side j θ| ≤ M₀) →
      ((n + 1 : ℕ) : ℝ) * M₀ * δ ≤ 1 →
      ∀ k, k ≤ N → ∀ p : PolarPoint,
        ‖iteratedFDeriv ℝ k
          (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q) p‖ ≤
            C * M ^ ((N + 1) * N + 2) ∧
        ‖iteratedFDeriv ℝ k
          (fun x => (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q x)⁻¹) p‖ ≤
            C * M ^ ((N + 1) * N + 2) := by
  obtain ⟨CT, hCT, hTaylor⟩ := exists_endpointTaylorCorrection_polynomial_envelope n N
  obtain ⟨CE, hCE, hExp⟩ := exists_exp_finiteJet_polynomial_envelope (E := PolarPoint) N
  let C₀ : ℝ := CE * Real.exp 2 * CT ^ N
  have hC₀ : 0 ≤ C₀ := by
    have hCT0 := zero_le_one.trans hCT
    have hCE0 := zero_le_one.trans hCE
    dsimp only [C₀]
    positivity
  refine ⟨1 + C₀, by linarith only [hC₀], ?_⟩
  intro M H M₀ δ hM hH hHM hM₀ hδ hδone hδinv l r q hdata hcoeff
    hpositive hupper hinverse hlog hsmall k hk p
  let A : Bool → ℕ → ℝ → ℝ := positiveHeightTaylorData l r (fun _ => 1) q
  let E : PolarPoint → ℝ := endpointTaylorCorrection n l r δ A
  let Q : PolarPoint → ℝ := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q
  let B : ℝ := CT * M ^ (N + 1)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hCT0 : 0 ≤ CT := zero_le_one.trans hCT
  have hCE0 : 0 ≤ CE := zero_le_one.trans hCE
  have hB : 1 ≤ B := by
    simpa only [one_mul] using
      (mul_le_mul hCT (one_le_pow₀ hM : 1 ≤ M ^ (N + 1)) zero_le_one hCT0)
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hE : ContDiff ℝ ∞ E := contDiff_endpointTaylorCorrection hdata l r δ
  have hjet (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j E p‖ ≤ B :=
    hTaylor hM hδ hδone hδinv l r A hdata hcoeff j hj p
  have hamp := positiveHeightTaylorInterpolation_amplitude n hδ hδone hM₀ hH
    hpositive hupper hinverse hlog hsmall p
  have hQ : Q = (fun x => Real.exp (E x)) := by
    funext x
    exact one_mul _
  have hQinv : (fun x => (Q x)⁻¹) = (fun x => Real.exp ((-E) x)) := by
    funext x
    rw [hQ, Pi.neg_apply, Real.exp_neg]
  have hbound (f : PolarPoint → ℝ) (hf : ContDiffAt ℝ ∞ f p)
      (hamp : Real.exp (f p) ≤ Real.exp 2 * H ^ 2)
      (hraw : ∀ j, 1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j f p‖ ≤ B) :
      ‖iteratedFDeriv ℝ k (fun x => Real.exp (f x)) p‖ ≤
        (1 + C₀) * M ^ ((N + 1) * N + 2) := by
    have hHsq : H ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (zero_le_one.trans hH) hHM 2
    have hpower : M ^ ((N + 1) * N + 2) = (M ^ (N + 1)) ^ N * M ^ 2 := by
      rw [pow_add, pow_mul]
    calc
      _ ≤ CE * (Real.exp 2 * H ^ 2) * B ^ N :=
        hExp hB (by positivity) f p hf hamp hraw k hk
      _ ≤ CE * (Real.exp 2 * M ^ 2) * B ^ N :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hHsq (Real.exp_pos 2).le) hCE0)
          (pow_nonneg hB0 _)
      _ = C₀ * M ^ ((N + 1) * N + 2) := by
        dsimp only [B, C₀]
        rw [mul_pow, hpower]
        ring
      _ ≤ (1 + C₀) * M ^ ((N + 1) * N + 2) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg hM0 _)
  change ‖iteratedFDeriv ℝ k Q p‖ ≤ _ ∧
    ‖iteratedFDeriv ℝ k (fun x => (Q x)⁻¹) p‖ ≤ _
  constructor
  · rw [hQ]
    apply hbound E hE.contDiffAt
    · simpa only [positiveHeightTaylorInterpolation, one_mul] using hamp.1
    · exact fun j _ hj => hjet j hj
  · rw [hQinv]
    apply hbound (-E) hE.neg.contDiffAt
    · rw [Pi.neg_apply, Real.exp_neg]
      simpa only [positiveHeightTaylorInterpolation, one_mul] using hamp.2
    · intro j _ hj
      rw [iteratedFDeriv_neg_apply, norm_neg]
      exact hjet j hj

end ContinuousFlexibility.Analysis
