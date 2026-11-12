import ContinuousFlexibility.Analysis.N01cCircleLinearVariationEnvelope
import ContinuousFlexibility.Analysis.N01cFlowHeadEnvelope

/-!
# Uniform angular envelopes for actual linear variation families

A fixed low coefficient integral and the one-high forcing polynomial
give a polynomial bound for the actual angular jets. The exponent and
the fixed aggregate order are chosen before the requested angular order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

theorem n01c_linearVariationFamily_angularEnvelope
    {I : Type*} {P : ℝ} [Fact (0 < P)]
    (V : I → CircleLinearVariationData P 0 1)
    (R : ℕ → I → ℝ) (H E : I → ℝ) (degree : ℕ) (L : ℝ)
    (hH : ∀ i, 0 ≤ H i) (hE : ∀ i, 1 ≤ E i)
    (hR : ∀ n i, 1 ≤ R n i)
    (hRmono : ∀ a b, a ≤ b → ∀ i, R a i ≤ R b i)
    (hL : ∀ i, (V i).coefficientSize 1 ≤ L)
    (hcoefficient : ∃ offset : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
        (V i).coefficientNorm s t ≤ A * R (s + offset) i * R offset i)
    (hforcing : ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
        (V i).forcingNorm s t ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
          R (s + offset) i * R offset i ^ degree) :
    ∃ offset : ℕ, ∀ b : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ : AddCircle P,
        |(V i).value t b θ| ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
          R (b + offset) i * R offset i ^ (degree + 2) := by
  obtain ⟨oa, ha⟩ := hcoefficient
  obtain ⟨oforce, hf⟩ := hforcing
  obtain ⟨B₁, hB₁, hb₁⟩ := hf 1
  let offset : ℕ := 1 + oa + oforce
  refine ⟨offset, fun b => ?_⟩
  obtain ⟨A, hA, hAb⟩ := ha (b + 1)
  obtain ⟨Bₛ, hBₛ, hbₛ⟩ := hf (b + 1)
  let F : ℝ := max Bₛ B₁
  have hF : 0 < F := hBₛ.trans_le (le_max_left _ _)
  let C : ℝ := circleSobolevEmbeddingConstant P *
    circleLinearVariationSobolevConstant P L (b + 1) * (F + A * F)
  obtain ⟨B, hB, habsorb⟩ :=
    exists_sameConstant_materialWeight_bound C F (3 / 4 : ℝ)
  refine ⟨B, hB, fun i t ht θ => ?_⟩
  let U : ℝ := R (b + offset) i
  let R₀ : ℝ := R offset i
  let W : ℝ := H i ^ (3 / 4 : ℝ) * E i ^ F
  have hU : 0 ≤ U := zero_le_one.trans (hR _ i)
  have hR₀ : 1 ≤ R₀ := hR _ i
  have hW : 0 ≤ W := mul_nonneg (Real.rpow_nonneg (hH i) _)
    (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
  have hweight (D : ℝ) (hD : 0 ≤ D) (hDF : D ≤ F) :
      D * H i ^ (3 / 4 : ℝ) * E i ^ D ≤ F * W := by
    simpa only [W, mul_assoc] using mul_le_mul
      (mul_le_mul_of_nonneg_right hDF (Real.rpow_nonneg (hH i) _))
      (Real.rpow_le_rpow_of_exponent_le (hE i) hDF)
      (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
      (mul_nonneg hF.le (Real.rpow_nonneg (hH i) _))
  have hcoef (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      (V i).coefficientNorm (b + 1) r ≤ A * U * R₀ :=
    (hAb i r hr).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left
        (hRmono _ _ (by dsimp only [offset]; omega) i) hA.le)
      (hRmono _ _ (by dsimp only [offset]; omega) i)
      (zero_le_one.trans (hR _ i)) (mul_nonneg hA.le hU))
  have hforce (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      (V i).forcingNorm (b + 1) r ≤ F * W * U * R₀ ^ degree :=
    (hbₛ i r hr).trans (mul_le_mul
      (mul_le_mul (hweight Bₛ hBₛ.le (le_max_left _ _))
        (hRmono _ _ (by dsimp only [offset]; omega) i)
        (zero_le_one.trans (hR _ i)) (mul_nonneg hF.le hW))
      (pow_le_pow_left₀ (zero_le_one.trans (hR _ i))
        (hRmono _ _ (by dsimp only [offset]; omega) i) degree)
      (pow_nonneg (zero_le_one.trans (hR _ i)) _) (by positivity))
  have hforceLow (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      (V i).forcingNorm 1 r ≤ F * W * R₀ ^ (degree + 1) := by
    have hh : (V i).forcingNorm 1 r ≤ F * W * R₀ * R₀ ^ degree :=
      (hb₁ i r hr).trans (mul_le_mul
        (mul_le_mul (hweight B₁ hB₁.le (le_max_right _ _))
          (hRmono _ _ (by dsimp only [offset]; omega) i)
          (zero_le_one.trans (hR _ i)) (mul_nonneg hF.le hW))
        (pow_le_pow_left₀ (zero_le_one.trans (hR _ i))
          (hRmono _ _ (by dsimp only [offset]; omega) i) degree)
        (pow_nonneg (zero_le_one.trans (hR _ i)) _) (by positivity))
    calc
      _ ≤ F * W * R₀ * R₀ ^ degree := hh
      _ = _ := by rw [pow_succ]; ring
  have hv := (V i).n01c_angular_value_le_polynomial b degree
    hA.le hF.le hW hU hR₀ ht (hL i) hcoef hforce hforceLow θ
  calc
    |(V i).value t b θ| ≤ C * W * U * R₀ ^ (degree + 2) := hv
    _ = C * H i ^ (3 / 4 : ℝ) * E i ^ F *
        (U * R₀ ^ (degree + 2)) := by dsimp only [W]; ring
    _ ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
        (U * R₀ ^ (degree + 2)) :=
      habsorb _ _ _ (hH i) (hE i)
        (mul_nonneg hU (pow_nonneg (zero_le_one.trans hR₀) _))
    _ = _ := by ring

end ContinuousFlexibility.Analysis
