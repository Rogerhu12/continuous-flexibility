import ContinuousFlexibility.Analysis.N01cFlowForcingEnvelope
import ContinuousFlexibility.Analysis.N01cFlowHeadEnvelope

/-!
# A uniform forcing envelope from actual head and lower factors

The finite partition formula is used before estimating. Its head keeps
the material weight, while the strict lower factors have scalar bounds.
Only one factor uses the requested spatial order; the degree depends on
the parameter order and never on the spatial order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem n01c_forcingFamily_envelope {I : Type*} (P : ℝ) (N : ℕ)
    (F R : ℕ → I → ℝ) (H E : I → ℝ)
    (f : ℕ → I → ∀ ω : FlowForcingChoice N, Fin (ω.1.length + 1) → ℝ)
    (hH : ∀ i, 0 ≤ H i) (hE : ∀ i, 1 ≤ E i)
    (hR : ∀ n i, 1 ≤ R n i)
    (hRmono : ∀ a b, a ≤ b → ∀ i, R a i ≤ R b i)
    (hf : ∀ s i ω j, 0 ≤ f s i ω j)
    (hmajorant : ∀ s i, F s i ≤ (2 : ℝ) ^ (s + 1) *
      ∑ ω : FlowForcingChoice N, circleProductSobolevConstant P ω.1.length s *
        ∑ j, f s i ω j * ∏ k ∈ Finset.univ.erase j, f 1 i ω k)
    (hhead : ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i ω,
      f s i ω 0 ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
        R (s + offset) i * R offset i)
    (hlower : ∃ offset : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ i ω j,
      f s i ω j.succ ≤ A * R (s + offset) i) :
    ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i,
      F s i ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
        R (s + offset) i * R offset i ^ (2 * N + 3) := by
  classical
  obtain ⟨oH, hhead⟩ := hhead
  obtain ⟨oL, hlower⟩ := hlower
  obtain ⟨B₁, hB₁, hh₁⟩ := hhead 1
  obtain ⟨A₁, hA₁, hl₁⟩ := hlower 1
  let offset : ℕ := 1 + oH + oL
  refine ⟨offset, fun s => ?_⟩
  obtain ⟨Bₛ, hBₛ, hhₛ⟩ := hhead s
  obtain ⟨Aₛ, hAₛ, hlₛ⟩ := hlower s
  let C : ℝ := max 1 (Bₛ + B₁ + Aₛ + A₁)
  have hC : 1 ≤ C := le_max_left _ _
  have hCBs : Bₛ ≤ C := by
    have h := le_max_right 1 (Bₛ + B₁ + Aₛ + A₁)
    dsimp only [C]
    linarith
  have hCB1 : B₁ ≤ C := by
    have h := le_max_right 1 (Bₛ + B₁ + Aₛ + A₁)
    dsimp only [C]
    linarith
  have hCAs : Aₛ ≤ C := by
    have h := le_max_right 1 (Bₛ + B₁ + Aₛ + A₁)
    dsimp only [C]
    linarith
  have hCA1 : A₁ ≤ C := by
    have h := le_max_right 1 (Bₛ + B₁ + Aₛ + A₁)
    dsimp only [C]
    linarith
  let A : ℝ := max Bₛ B₁
  let K : ℝ := (2 : ℝ) ^ (s + 1) *
    (∑ ω : FlowForcingChoice N, circleProductSobolevConstant P ω.1.length s) *
      ((N : ℝ) + 1) * C ^ (N + 2)
  obtain ⟨B, hB, habsorb⟩ :=
    exists_sameConstant_materialWeight_bound K A (3 / 4 : ℝ)
  refine ⟨B, hB, fun i => ?_⟩
  let W : ℝ := H i ^ (3 / 4 : ℝ) * E i ^ A
  let U : ℝ := R (s + offset) i
  let R₀ : ℝ := R offset i
  have hW : 0 ≤ W := mul_nonneg (Real.rpow_nonneg (hH i) _)
    (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
  have hU : 0 ≤ U := zero_le_one.trans (hR _ i)
  have hR₀ : 1 ≤ R₀ := hR _ i
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hweight (D : ℝ) (hD : 0 ≤ D) (hDC : D ≤ C) (hDA : D ≤ A) :
      D * H i ^ (3 / 4 : ℝ) * E i ^ D ≤ C * W := by
    simpa only [W, mul_assoc] using mul_le_mul
      (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg (hH i) _))
      (Real.rpow_le_rpow_of_exponent_le (hE i) hDA)
      (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
      (mul_nonneg hC0 (Real.rpow_nonneg (hH i) _))
  have hheadHigh (ω : FlowForcingChoice N) : f s i ω 0 ≤ C * W * U * R₀ := by
    apply (hhₛ i ω).trans
    exact mul_le_mul
      (mul_le_mul (hweight Bₛ hBₛ.le hCBs (le_max_left _ _))
        (hRmono _ _ (by dsimp only [offset]; omega) i)
        (zero_le_one.trans (hR _ i)) (mul_nonneg hC0 hW))
      (hRmono _ _ (by dsimp only [offset]; omega) i)
      (zero_le_one.trans (hR _ i)) (by positivity)
  have hheadLow (ω : FlowForcingChoice N) : f 1 i ω 0 ≤ C * W * R₀ ^ 2 := by
    have hh : f 1 i ω 0 ≤ C * W * R₀ * R₀ := (hh₁ i ω).trans (mul_le_mul
      (mul_le_mul (hweight B₁ hB₁.le hCB1 (le_max_right _ _))
        (hRmono _ _ (by dsimp only [offset]; omega) i)
        (zero_le_one.trans (hR _ i)) (mul_nonneg hC0 hW))
      (hRmono _ _ (by dsimp only [offset]; omega) i)
      (zero_le_one.trans (hR _ i)) (by positivity))
    nlinarith [hh]
  have hotherHigh (ω : FlowForcingChoice N) (j : Fin ω.1.length) :
      f s i ω j.succ ≤ C * U :=
    (hlₛ i ω j).trans (mul_le_mul hCAs
      (hRmono _ _ (by dsimp only [offset]; omega) i)
      (zero_le_one.trans (hR _ i)) hC0)
  have hotherLow (ω : FlowForcingChoice N) (j : Fin ω.1.length) :
      f 1 i ω j.succ ≤ C * R₀ :=
    (hl₁ i ω j).trans (mul_le_mul hCA1
      (hRmono _ _ (by dsimp only [offset]; omega) i)
      (zero_le_one.trans (hR _ i)) hC0)
  have hnumeric := n01c_forcingMajorant_polynomial P N s
    (f s i) (f 1 i) hC hW hU hR₀ (hf s i) (hf 1 i)
    hheadHigh hheadLow hotherHigh hotherLow
  calc
    F s i ≤ (2 : ℝ) ^ (s + 1) *
        ∑ ω : FlowForcingChoice N, circleProductSobolevConstant P ω.1.length s *
          ∑ j, f s i ω j * ∏ k ∈ Finset.univ.erase j, f 1 i ω k := hmajorant s i
    _ ≤ K * W * U * R₀ ^ (2 * N + 3) := hnumeric
    _ = K * H i ^ (3 / 4 : ℝ) * E i ^ A *
        (U * R₀ ^ (2 * N + 3)) := by dsimp only [W]; ring
    _ ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
        (U * R₀ ^ (2 * N + 3)) :=
      habsorb _ _ _ (hH i) (hE i)
        (mul_nonneg hU (pow_nonneg (zero_le_one.trans hR₀) _))
    _ = _ := by ring

end ContinuousFlexibility.Analysis
