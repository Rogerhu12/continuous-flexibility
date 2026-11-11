import ContinuousFlexibility.Analysis.OneHighCircleFlowNormContinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The genuine circle Sobolev norm of a time integral

The canonical continuous-map-to-`L²` linear map commutes with the Bochner
time integral. Its norm inequality gives Minkowski for the actual circle
`L²` norms. Applying this to the zeroth and highest actual derivatives
proves the corresponding physical Sobolev bound, with all time
integrability derived from continuity of the derivative family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem circle_norm_toLp (f : C(AddCircle P, ℝ)) :
    ‖ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ f‖ =
      (eLpNorm f 2 AddCircle.haarAddCircle).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := AddCircle.haarAddCircle) (𝕜 := ℝ) f)]

theorem continuousOn_circleRealSobolevNorm_of_derivatives
    (f : ℝ → ℕ → C(AddCircle P, ℝ)) {a b : ℝ}
    (hderiv : ∀ t ∈ Icc a b, ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f t k (y : AddCircle P))
        (f t (k + 1) (x : AddCircle P)) x)
    (s : ℕ) (hzero : ContinuousOn (fun t => f t 0) (Icc a b))
    (hs : ContinuousOn (fun t => f t s) (Icc a b)) :
    ContinuousOn (fun t => circleRealSobolevNorm (s : ℝ) (f t 0)) (Icc a b) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_circleRealSobolevNorm_of_derivatives
    (fun t : Icc a b => f t) (fun t => hderiv t t.property) s hzero.domRestrict hs.domRestrict

/-- Minkowski for a continuous family of genuine continuous circle functions. -/
theorem circle_l2_intervalIntegral_le (f : ℝ → C(AddCircle P, ℝ))
    {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (eLpNorm ((∫ t in a..b, f t) : C(AddCircle P, ℝ)) 2 AddCircle.haarAddCircle).toReal ≤
      ∫ t in a..b, (eLpNorm (f t) 2 AddCircle.haarAddCircle).toReal := by
  let L : C(AddCircle P, ℝ) →L[ℝ] Lp ℝ 2 AddCircle.haarAddCircle :=
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ
  have hI : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  rw [← circle_norm_toLp, ← L.intervalIntegral_comp_comm hI]
  have hh := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t => L (f t)) hab
  simpa only [L, circle_norm_toLp] using hh

/-- The actual Sobolev norm of a time integral is controlled by the time
integral of the actual source Sobolev norms. The harmless finite-order
constant comes from the existing Bessel/physical-derivative comparison. -/
theorem circle_real_sobolevNorm_intervalIntegral_le
    (F : ℕ → C(AddCircle P, ℝ)) (f : ℝ → ℕ → C(AddCircle P, ℝ))
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => F k (y : AddCircle P))
        (F (k + 1) (x : AddCircle P)) x)
    (hf : ∀ t ∈ Icc a b, ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f t k (y : AddCircle P))
        (f t (k + 1) (x : AddCircle P)) x)
    (hcontinuous : ∀ k : ℕ, ContinuousOn (fun t => f t k) (Icc a b))
    (hidentity : ∀ k : ℕ, ∀ x : AddCircle P, F k x = ∫ t in a..b, f t k x)
    (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (F 0) ≤ (2 : ℝ) ^ (s + 1) *
      ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0) := by
  have hnorm := continuousOn_circleRealSobolevNorm_of_derivatives f hf s
    (hcontinuous 0) (hcontinuous s)
  have heq (k : ℕ) : F k = ∫ t in a..b, f t k := by
    ext x
    have hIk : IntervalIntegrable (fun t => f t k) volume a b :=
      (hcontinuous k).intervalIntegrable_of_Icc hab
    have hh := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hIk
    have heval : (∫ t in a..b, f t k x) =
        ((∫ t in a..b, f t k) : C(AddCircle P, ℝ)) x := by
      simpa only [ContinuousMap.evalCLM_apply] using hh
    exact (hidentity k x).trans heval
  have hL2 (k : ℕ) (hks : k ≤ s) :
      (eLpNorm (F k) 2 AddCircle.haarAddCircle).toReal ≤
        ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0) := by
    have hc : ContinuousOn
        (fun t => (eLpNorm (f t k) 2 AddCircle.haarAddCircle).toReal) (Icc a b) := by
      have hh := ((ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ).continuous.comp_continuousOn
        (hcontinuous k)).norm
      simpa only [Function.comp_def, circle_norm_toLp] using hh
    calc
      _ = (eLpNorm ((∫ t in a..b, f t k) : C(AddCircle P, ℝ)) 2 AddCircle.haarAddCircle).toReal := by rw [heq k]
      _ ≤ ∫ t in a..b, (eLpNorm (f t k) 2 AddCircle.haarAddCircle).toReal :=
        circle_l2_intervalIntegral_le (fun t => f t k) hab (hcontinuous k)
      _ ≤ ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0) :=
        intervalIntegral.integral_mono_on (μ := volume) hab
          (hc.intervalIntegrable_of_Icc hab) (hnorm.intervalIntegrable_of_Icc hab)
          (fun t ht => circle_real_derivative_l2_le_sobolev (f t) (hf t ht) hks)
  calc
    circleRealSobolevNorm (s : ℝ) (F 0) ≤ (2 : ℝ) ^ s *
        ((eLpNorm (F 0) 2 AddCircle.haarAddCircle).toReal +
          (eLpNorm (F s) 2 AddCircle.haarAddCircle).toReal) :=
      circle_real_sobolevNorm_le_derivative_endpoints F hF s
    _ ≤ (2 : ℝ) ^ s *
        ((∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0)) +
          ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (f t 0)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hL2 0 (Nat.zero_le s)) (hL2 s le_rfl)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end ContinuousFlexibility.Analysis
