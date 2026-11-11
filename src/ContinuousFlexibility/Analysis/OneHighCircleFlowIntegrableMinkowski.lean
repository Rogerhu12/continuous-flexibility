import ContinuousFlexibility.Analysis.OneHighCircleFlowMinkowski

/-!
# Sobolev Minkowski for integrable time families

The reference angular speed in the translation comparison need only be
integrable in time. The continuous-map-to-L² linear map commutes with
its Bochner integral just as it does for a continuous time family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem circle_l2_intervalIntegral_le_of_integrable
    (f : ℝ → C(AddCircle P, ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    (eLpNorm ((∫ t in a..b, f t) : C(AddCircle P, ℝ)) 2 AddCircle.haarAddCircle).toReal ≤
      ∫ t in a..b, (eLpNorm (f t) 2 AddCircle.haarAddCircle).toReal := by
  let L : C(AddCircle P, ℝ) →L[ℝ] Lp ℝ 2 AddCircle.haarAddCircle :=
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ
  rw [← circle_norm_toLp, ← L.intervalIntegral_comp_comm hf]
  have hh := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t => L (f t)) hab
  simpa only [L, circle_norm_toLp] using hh

/-- Actual derivative towers permit the same Sobolev integral estimate
for merely integrable time families. The norm integrability hypothesis
is discharged from the data in the translation application. -/
theorem circle_real_sobolevNorm_intervalIntegral_le_of_integrable
    (F : ℕ → C(AddCircle P, ℝ)) (f : ℝ → ℕ → C(AddCircle P, ℝ))
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => F k (y : AddCircle P))
        (F (k + 1) (x : AddCircle P)) x)
    (hf : ∀ t ∈ Icc a b, ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f t k (y : AddCircle P))
        (f t (k + 1) (x : AddCircle P)) x)
    (hintegrable : ∀ k : ℕ, IntervalIntegrable (fun t => f t k) volume a b)
    (hidentity : ∀ k : ℕ, ∀ x : AddCircle P, F k x = ∫ t in a..b, f t k x)
    (s : ℕ)
    (hnorm : IntervalIntegrable
      (fun t => circleRealSobolevNorm (s : ℝ) (f t 0)) volume a b) :
    circleRealSobolevNorm (s : ℝ) (F 0) ≤ (2 : ℝ) ^ (s + 1) *
      ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0) := by
  have heq (k : ℕ) : F k = ∫ t in a..b, f t k := by
    ext x
    have hh := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm (hintegrable k)
    have heval : (∫ t in a..b, f t k x) =
        ((∫ t in a..b, f t k) : C(AddCircle P, ℝ)) x := by
      simpa only [ContinuousMap.evalCLM_apply] using hh
    exact (hidentity k x).trans heval
  have hL2 (k : ℕ) (hks : k ≤ s) :
      (eLpNorm (F k) 2 AddCircle.haarAddCircle).toReal ≤
        ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0) := by
    let L : C(AddCircle P, ℝ) →L[ℝ] Lp ℝ 2 AddCircle.haarAddCircle :=
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ
    have hI : IntervalIntegrable (fun t => L (f t k)) volume a b :=
      ⟨L.integrable_comp (hintegrable k).1, L.integrable_comp (hintegrable k).2⟩
    have hnormI : IntervalIntegrable
        (fun t => (eLpNorm (f t k) 2 AddCircle.haarAddCircle).toReal) volume a b := by
      simpa only [L, circle_norm_toLp] using hI.norm
    calc
      _ = (eLpNorm ((∫ t in a..b, f t k) : C(AddCircle P, ℝ)) 2 AddCircle.haarAddCircle).toReal := by rw [heq k]
      _ ≤ ∫ t in a..b, (eLpNorm (f t k) 2 AddCircle.haarAddCircle).toReal :=
        circle_l2_intervalIntegral_le_of_integrable (fun t => f t k) hab (hintegrable k)
      _ ≤ ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0) :=
        intervalIntegral.integral_mono_on (μ := volume) hab hnormI hnorm
          (fun t ht => circle_real_derivative_l2_le_sobolev (f t) (hf t ht) hks)
  calc
    circleRealSobolevNorm (s : ℝ) (F 0) ≤ (2 : ℝ) ^ s *
        ((eLpNorm (F 0) 2 AddCircle.haarAddCircle).toReal +
          (eLpNorm (F s) 2 AddCircle.haarAddCircle).toReal) :=
      circle_real_sobolevNorm_le_derivative_endpoints F hF s
    _ ≤ (2 : ℝ) ^ s *
        ((∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0)) +
          ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (hL2 0 (Nat.zero_le s)) (hL2 s le_rfl)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end ContinuousFlexibility.Analysis
