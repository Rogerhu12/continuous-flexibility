import ContinuousFlexibility.Analysis.N01cFlowNumericConstants
import ContinuousFlexibility.Analysis.OneHighCircleFlowReferenceNorms
import ContinuousFlexibility.Analysis.OneHighCircleFourierLiftBounds

/-!
# Uniform zero-parameter circle-flow growth

These estimates concern the supplied classical trajectories. The low
integrated speed norm is bounded once. Every high estimate then uses the
actual reference norm of that speed and the actual derivative defect.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

theorem circleFlow_positiveAngular_le_defect
    {P : ℝ} [Fact (0 < P)] {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) (θ : ℝ) :
    |iteratedDeriv (n + 1) (fun η => Θ (t, η)) θ| ≤
      circleSobolevEmbeddingConstant P *
        circleRealSobolevNorm ((n + 1 : ℕ) : ℝ)
          (circleFlowDefectJet hG hperiod hΘ hinit hflow t 0) + 1 := by
  let Q := circleFlowDefectJet hG hperiod hΘ hinit hflow t
  have hQ := circleFlowDefectJet_hasDerivAt hG hperiod hΘ hinit hflow ht
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  have hnorm : circleRealSobolevNorm 1 (Q n) ≤
      circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (Q 0) := by
    simpa only [Nat.cast_one, Nat.add_comm 1 n] using
      circle_real_sobolevNorm_derivative_le Q hQ 1 n
  have hpoint :=
    (circle_real_norm_apply_le_sobolev_one_of_derivatives Q hQ n
      (θ : AddCircle P)).trans (mul_le_mul_of_nonneg_left hnorm hE)
  have heq : iteratedDeriv (n + 1) (fun η => Θ (t, η)) θ =
      Q n (θ : AddCircle P) + if n = 0 then 1 else 0 := by
    have he := circleFlowDefectJet_coe_apply hG hperiod hΘ hinit hflow ht n θ
    change Q n (θ : AddCircle P) = _ at he
    exact (eq_sub_iff_add_eq.mp he).symm
  have hcorr : ‖(if n = 0 then (1 : ℝ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  rw [← Real.norm_eq_abs, heq]
  exact (norm_add_le _ _).trans (add_le_add hpoint hcorr)

/-- A family version keeps every existential and high-order constant
independent of the representation of its parameter space. -/
theorem circleFlow_family_zeroAngular_growth
    {X I : Type*} {P : ℝ} [Fact (0 < P)]
    (U : Set X) (size : ℕ → X → ℝ)
    (hsize : ∀ n x, x ∈ U → 0 ≤ size n x)
    (G Θ : X → I → PolarPoint → ℝ) (c : I → ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) (τ : ℕ)
    (hG : ∀ x, x ∈ U → ∀ m, ContDiff ℝ ∞ (G x m))
    (hperiod : ∀ x, x ∈ U → ∀ m t,
      Function.Periodic (fun θ => G x m (t, θ)) P)
    (hΘ : ∀ x, x ∈ U → ∀ m θ,
      ContinuousOn (fun t => Θ x m (t, θ)) (Icc a b))
    (hinit : ∀ x, x ∈ U → ∀ m θ, Θ x m (a, θ) = θ)
    (hflow : ∀ x, x ∈ U → ∀ m t, t ∈ Ioo a b → ∀ θ,
      HasDerivAt (fun r => Θ x m (r, θ))
        (G x m (t, Θ x m (t, θ))) t)
    (hc : ∀ m, IntervalIntegrable (c m) volume a b)
    (M : ℝ)
    (hlow : ∀ x (hx : x ∈ U) m,
      circleFlowLambda (G x m) (hG x hx m) (hperiod x hx m) 4 a b ≤ M)
    (href : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x (hx : x ∈ U) m,
      circleFlowReferenceSize (G x m) (hG x hx m) (hperiod x hx m)
        (c m) s a b ≤ C * (1 + size (s + τ) x)) :
    (∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x (hx : x ∈ U) m t, t ∈ Icc a b →
      circleRealSobolevNorm (s : ℝ)
        (circleFlowDefectJet (hG x hx m) (hperiod x hx m)
          (hΘ x hx m) (hinit x hx m) (hflow x hx m) t 0) ≤
        C * (1 + size (s + 1 + τ) x)) ∧
    (∀ β : ℕ, 1 ≤ β → ∃ C : ℝ, 0 < C ∧
      ∀ x (hx : x ∈ U) m t, t ∈ Icc a b → ∀ θ,
        |iteratedDeriv β (fun η => Θ x m (t, η)) θ| ≤
          C * (1 + size (β - 1 + (τ + 2)) x)) := by
  have hdefect : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x (hx : x ∈ U) m t,
      t ∈ Icc a b →
        circleRealSobolevNorm (s : ℝ)
          (circleFlowDefectJet (hG x hx m) (hperiod x hx m)
            (hΘ x hx m) (hinit x hx m) (hflow x hx m) t 0) ≤
          C * (1 + size (s + 1 + τ) x) := by
    intro s
    obtain ⟨K, hK, hKunif⟩ := exists_circleFlowSobolevConstant_uniform P M s
    obtain ⟨C, hC, hCbound⟩ := href (s + 1)
    refine ⟨K * C, mul_pos hK hC, ?_⟩
    intro x hx m t ht
    have hL := circleFlowLambda_nonneg (G x m) (hG x hx m) (hperiod x hx m) s hab
    have hKbound := hKunif _ ⟨circleFlowLambda_nonneg
      (G x m) (hG x hx m) (hperiod x hx m) 4 hab, hlow x hx m⟩
    calc
      _ ≤ circleFlowSobolevConstant P
          (circleFlowLambda (G x m) (hG x hx m) (hperiod x hx m) 4 a b) s *
          circleFlowLambda (G x m) (hG x hx m) (hperiod x hx m) s a b :=
        circleFlow_defect_sobolev_le (hG x hx m) (hperiod x hx m)
          (hΘ x hx m) (hinit x hx m) (hflow x hx m) s ht
      _ ≤ K * circleFlowLambda (G x m) (hG x hx m) (hperiod x hx m) s a b :=
        mul_le_mul_of_nonneg_right hKbound hL
      _ ≤ K * circleFlowReferenceSize (G x m) (hG x hx m)
          (hperiod x hx m) (c m) (s + 1) a b :=
        mul_le_mul_of_nonneg_left (circleFlowLambda_le_referenceSize
          (G x m) (hG x hx m) (hperiod x hx m) hab (hc m) s) hK.le
      _ ≤ K * (C * (1 + size (s + 1 + τ) x)) :=
        mul_le_mul_of_nonneg_left (hCbound x hx m) hK.le
      _ = _ := by rw [mul_assoc]
  refine ⟨hdefect, ?_⟩
  intro β hβ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
  obtain ⟨C, hC, hCbound⟩ := hdefect (n + 1)
  let E : ℝ := circleSobolevEmbeddingConstant P
  have hE : 0 < E := zero_lt_one.trans_le (circleSobolevEmbeddingConstant_one_le P)
  refine ⟨E * C + 1, by positivity, ?_⟩
  intro x hx m t ht θ
  have hn : n + 1 + 1 + τ = (n + 1) - 1 + (τ + 2) := by omega
  have hpoint := circleFlow_positiveAngular_le_defect (hG x hx m) (hperiod x hx m)
    (hΘ x hx m) (hinit x hx m) (hflow x hx m) ht n θ
  have hq := hCbound x hx m t ht
  rw [hn] at hq
  have hs := hsize ((n + 1) - 1 + (τ + 2)) x hx
  calc
    _ ≤ E * circleRealSobolevNorm ((n + 1 : ℕ) : ℝ)
        (circleFlowDefectJet (hG x hx m) (hperiod x hx m)
          (hΘ x hx m) (hinit x hx m) (hflow x hx m) t 0) + 1 := hpoint
    _ ≤ E * (C * (1 + size ((n + 1) - 1 + (τ + 2)) x)) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hq hE.le) le_rfl
    _ ≤ (E * C + 1) * (1 + size ((n + 1) - 1 + (τ + 2)) x) := by
      nlinarith

/-- Transport a genuine pointwise family estimate through a scalar
comparison without exposing the parameter-space implementation. -/
theorem angularGrowth_of_pointwiseComparison
    {X J : Type*} (U : Set X) (size : ℕ → X → ℝ)
    (hsize : ∀ n x, x ∈ U → 0 ≤ size n x)
    (left right : ℕ → ℝ) (F : ℕ → PolarPoint → X → ℝ)
    (A : ∀ s : ℕ, ∀ x, x ∈ U → J → ℝ)
    (geom : ℕ → ℝ) (hgeom : ∀ s, 0 < geom s) (τ : ℕ)
    (hcompare : ∀ s x (hx : x ∈ U) M, 0 ≤ M →
      (∀ m b q, b ≤ s → q.1 ∈ Ioo (left m) (right m) → |F b q x| ≤ M) →
        ∀ j, A s x hx j ≤ geom s * M)
    (hraw : ∀ s : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ x ∈ U, ∀ m b q,
      b ≤ s → q.1 ∈ Ioo (left m) (right m) →
        |F b q x| ≤ M * (1 + size (s + τ) x)) :
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x (hx : x ∈ U) j,
      A s x hx j ≤ C * (1 + size (s + τ) x) := by
  intro s
  obtain ⟨M, hM, hb⟩ := hraw s
  refine ⟨geom s * M, mul_pos (hgeom s) hM, ?_⟩
  intro x hx j
  have hW : 0 ≤ 1 + size (s + τ) x := add_nonneg zero_le_one (hsize _ x hx)
  simpa only [mul_assoc] using hcompare s x hx
    (M * (1 + size (s + τ) x)) (mul_nonneg hM.le hW) (hb x hx) j

/-- A surjective time change transfers angular estimates of the same
trajectories without differentiating the inverse time coordinate. -/
theorem angularGrowth_surjectiveTimeChange
    {X I : Type*} (U : Set X) (size : ℕ → X → ℝ) (offset : ℕ)
    (Θ : X → I → PolarPoint → ℝ) (F : X → I → ℝ → ℝ → ℝ)
    (path : I → ℝ → ℝ) (time : Set ℝ) (radius : I → Set ℝ)
    (hsurj : ∀ m, SurjOn (path m) time (radius m))
    (heq : ∀ x, x ∈ U → ∀ m t, t ∈ time → ∀ θ,
      Θ x m (t, θ) = F x m (path m t) θ)
    (hbound : ∀ β : ℕ, 1 ≤ β → ∃ C : ℝ, 0 < C ∧
      ∀ x, x ∈ U → ∀ m t, t ∈ time → ∀ θ,
        |iteratedDeriv β (fun η => Θ x m (t, η)) θ| ≤
          C * (1 + size (β - 1 + offset) x)) :
    ∀ β : ℕ, 1 ≤ β → ∃ C : ℝ, 0 < C ∧
      ∀ x, x ∈ U → ∀ m r, r ∈ radius m → ∀ θ,
        |iteratedDeriv β (F x m r) θ| ≤
          C * (1 + size (β - 1 + offset) x) := by
  intro β hβ
  obtain ⟨C, hC, hb⟩ := hbound β hβ
  refine ⟨C, hC, ?_⟩
  intro x hx m r hr θ
  obtain ⟨t, ht, htr⟩ := hsurj m hr
  have hfun : (fun η => Θ x m (t, η)) = F x m r := by
    funext η
    rw [heq x hx m t ht η, htr]
  simpa only [hfun] using hb x hx m t ht θ

end ContinuousFlexibility.Analysis
