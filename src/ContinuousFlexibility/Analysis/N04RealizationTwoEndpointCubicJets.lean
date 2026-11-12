import ContinuousFlexibility.Analysis.N04RealizationOneEndpointCubicJets

/-!
# Actual parameter jets after both cubic divisions

The first quotient is ordinary division on the open cylinder. Its
reflected smooth representative has the required zero jets for the
second division. Applying the same one-endpoint theorem twice gives six
radial orders of loss, with no change to the parameter neighborhood and
no angular loss. The output is the original field in the factorization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {R : ℝ} {N e : E → PolarPoint → ℝ}

/-- Both endpoint divisions preserve the genuine mixed tower and transfer
the numerator's continuous majorants with a fixed radial loss of six.
The harmless numerical constant is uniform in the interval width and
in every spatial and parameter order. -/
theorem n04Realization_twoEndpointCubic_parameterJets
    (hU : IsOpen U) (hR : 0 < R)
    (RN : MixedJetRegularity U (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) N)
    (hrep : ∀ x ∈ U, ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (N x) (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) ∧
      ∀ c : Bool, ∀ θ i, i ≤ 2 →
        iteratedDeriv i (fun r : ℝ => F (r, θ)) (if c then R else 0) = 0)
    (hfactor : ∀ x ∈ U, ∀ q ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ),
      N x q = (q.1 * (R - q.1)) ^ 3 * e x q)
    (G : ∀ k : ℕ, ℕ → ℕ → E × (Fin k → E) → ℝ)
    (hG : ∀ k a b, Continuous (G k a b))
    (hbound : ∀ k a b q (hq : q ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)),
      ∀ x ∈ U, ∀ v : Fin k → E,
        |(RN.parameter a b q hq).D k x v| ≤ G k a b (x, v)) :
    ∃ RE : MixedJetRegularity U (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) e,
      ∀ k a b p (hp : p ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)),
        ∀ x ∈ U, ∀ v : Fin k → E,
          |(RE.parameter a b p hp).D k x v| ≤ G k (a + 6) b (x, v) / 4 := by
  let Ω : Set PolarPoint := Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  let RE : MixedJetRegularity U Ω e :=
    n04Realization_mixedJetRegularity_of_staticFactorization RN hU hΩ
      ((contDiff_fst.mul (contDiff_const.sub contDiff_fst)).pow 3).contDiffOn
      (fun q hq => pow_ne_zero 3
        (mul_pos hq.1.1 (sub_pos.mpr hq.1.2)).ne') hfactor
  let e₁ : E → PolarPoint → ℝ := fun x q => N x q / q.1 ^ 3
  have hf₁ : ∀ x ∈ U, ∀ q ∈ Ω, N x q = q.1 ^ 3 * e₁ x q := by
    intro x hx q hq
    dsimp only [e₁]
    field_simp [pow_ne_zero 3 hq.1.1.ne'] <;> ring
  let R₁ : MixedJetRegularity U Ω e₁ :=
    n04Realization_mixedJetRegularity_of_staticFactorization RN hU hΩ
      (contDiff_fst.pow 3).contDiffOn
      (fun q hq => pow_ne_zero 3 hq.1.1.ne') hf₁
  have hr₁ : ∀ x ∈ U, ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (N x) Ω ∧
      ∀ θ i, i ≤ 2 → iteratedDeriv i (fun r : ℝ => F (r, θ)) 0 = 0 := by
    intro x hx
    obtain ⟨F, hF, he, hz⟩ := hrep x hx
    exact ⟨F, hF, he, fun θ i hi => by simpa using hz false θ i hi⟩
  have hb₁ (k a b : ℕ) (q : PolarPoint) (hq : q ∈ Ω)
      (x : E) (hx : x ∈ U) (v : Fin k → E) :
      |(R₁.parameter a b q hq).D k x v| ≤ G k (a + 3) b (x, v) / 2 :=
    n04Realization_oneEndpointCubic_parameterJets RN hr₁ hf₁ G hG hbound
      a b q hq (R₁.parameter a b q hq) k x hx v
  let e₂ : E → PolarPoint → ℝ := fun x => reflectRadialField R (e₁ x)
  let R₂ : MixedJetRegularity U Ω e₂ := n04Realization_mixedJetRegularity_reflect R₁
  let er : E → PolarPoint → ℝ := fun x => reflectRadialField R (e x)
  let Rer : MixedJetRegularity U Ω er := n04Realization_mixedJetRegularity_reflect RE
  have hr₂ : ∀ x ∈ U, ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (e₂ x) Ω ∧
      ∀ θ i, i ≤ 2 → iteratedDeriv i (fun r : ℝ => F (r, θ)) 0 = 0 := by
    intro x hx
    obtain ⟨F, hF, he, hz⟩ := hrep x hx
    have hl : ∀ θ i, i ≤ 2 → iteratedDeriv i (fun r : ℝ => F (r, θ)) 0 = 0 := by
      intro θ i hi
      simpa using hz false θ i hi
    have hr : ∀ θ i, i ≤ 2 → iteratedDeriv i (fun r : ℝ => F (r, θ)) R = 0 := by
      intro θ i hi
      simpa using hz true θ i hi
    obtain ⟨h0, h1, h2⟩ := radialBoundaryPartials_of_sliceJets hF 0 hl
    refine ⟨reflectRadialField R (radialCubicQuotient F),
      contDiff_reflectRadialField R (contDiff_radialCubicQuotient hF h0 h1 h2), ?_,
      reflectedRadialCubicQuotient_zero_jets hF hR hl hr⟩
    intro q hq
    have hqr := n04Realization_reflect_mem_cylinder hq
    change radialCubicQuotient F (R - q.1, q.2) =
      N x (R - q.1, q.2) / (R - q.1) ^ 3
    apply (eq_div_iff (pow_ne_zero 3 hqr.1.1.ne')).mpr
    calc
      radialCubicQuotient F (R - q.1, q.2) * (R - q.1) ^ 3 =
          F (R - q.1, q.2) := by
        simpa only [mul_comm] using cube_mul_cubicQuotient (h0 q.2) (R - q.1)
      _ = N x (R - q.1, q.2) := he hqr
  have hf₂ : ∀ x ∈ U, ∀ q ∈ Ω, e₂ x q = q.1 ^ 3 * er x q := by
    intro x hx q hq
    have hqr := n04Realization_reflect_mem_cylinder hq
    change N x (R - q.1, q.2) / (R - q.1) ^ 3 =
      q.1 ^ 3 * e x (R - q.1, q.2)
    rw [hfactor x hx _ hqr]
    have he : R - (R - q.1) = q.1 := by ring
    simp only [he]
    field_simp [pow_ne_zero 3 hqr.1.1.ne'] <;> ring
  let G₂ : ∀ k : ℕ, ℕ → ℕ → E × (Fin k → E) → ℝ :=
    fun k a b y => G k (a + 3) b y / 2
  have hG₂ : ∀ k a b, Continuous (G₂ k a b) :=
    fun k a b => (hG k (a + 3) b).div_const 2
  have hb₂ (k a b : ℕ) (q : PolarPoint) (hq : q ∈ Ω)
      (x : E) (hx : x ∈ U) (v : Fin k → E) :
      |(R₂.parameter a b q hq).D k x v| ≤ G₂ k a b (x, v) := by
    have hqr := n04Realization_reflect_mem_cylinder hq
    have he := n04Realization_smoothDirections_D_const_mul
      (R₁.parameter a b (R - q.1, q.2) hqr) (R₂.parameter a b q hq)
      ((-1 : ℝ) ^ a)
      (fun y _ => mixedDerivative_reflectRadialField R (e₁ y) a b q) k hx v
    rw [he, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hb₁ k a b (R - q.1, q.2) hqr x hx v
  refine ⟨RE, ?_⟩
  intro k a b p hp x hx v
  have hpr := n04Realization_reflect_mem_cylinder hp
  let Q : SmoothDirections U (fun y => mixedDerivative a b (er y) (R - p.1, p.2)) :=
    Rer.parameter a b (R - p.1, p.2) hpr
  have hb := n04Realization_oneEndpointCubic_parameterJets R₂ hr₂ hf₂ G₂ hG₂ hb₂
    a b (R - p.1, p.2) hpr Q k x hx v
  have he := n04Realization_smoothDirections_D_const_mul
    (RE.parameter a b p hp) Q ((-1 : ℝ) ^ a)
    (fun y _ => by
      have hpp : (R - (R - p.1), p.2) = p := by
        apply Prod.ext
        · ring
        · rfl
      simpa only [Prod.fst, Prod.snd, hpp] using
        mixedDerivative_reflectRadialField R (e y) a b (R - p.1, p.2)) k hx v
  rw [he, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at hb
  calc
    |(RE.parameter a b p hp).D k x v| ≤
        (G k ((a + 3) + 3) b (x, v) / 2) / 2 := hb
    _ = G k (a + 6) b (x, v) / 4 := by
      rw [Nat.add_assoc]
      norm_num only [Nat.reduceAdd]
      ring

end ContinuousFlexibility.Analysis
