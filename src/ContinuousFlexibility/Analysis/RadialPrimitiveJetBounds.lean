module

public import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveJets
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
public import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegral

/-!
# Linear jet bounds for the actual radial primitive

Angular derivatives pass through the displayed radial integral. A positive
number of radial derivatives removes that integral. The resulting bound
is linear in the integrand jets and uses the same fixed integration base.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff Interval

def radialIntervalPrimitive (l : ℝ) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  ∫ t in l..p.1, f (t, p.2)

theorem contDiff_radialIntervalPrimitive {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : ℝ) :
    ContDiff ℝ ∞ (radialIntervalPrimitive l f) := by
  have hswap : ContDiff ℝ ∞ (fun p : PolarPoint => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  exact (contDiff_parametric_primitive (hf.comp hswap) l).comp hswap

theorem mixedDerivative_radialIntervalPrimitive_zero {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : ℝ) (b : ℕ) :
    mixedDerivative 0 b (radialIntervalPrimitive l f) =
      radialIntervalPrimitive l (mixedDerivative 0 b f) := by
  have hswap : ContDiff ℝ ∞ (fun p : PolarPoint => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  funext p
  have h := iteratedDeriv_intervalIntegral_parameter
    (f := fun q : ℝ × ℝ => f (q.2, q.1)) (hf.comp hswap) b l p.1 p.2
  simpa only [mixedDerivative, iteratedDeriv_zero, radialIntervalPrimitive] using h

theorem mixedDerivative_radialIntervalPrimitive_succ {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : ℝ) (a b : ℕ) :
    mixedDerivative (a + 1) b (radialIntervalPrimitive l f) =
      mixedDerivative a b f := by
  have hzero := mixedDerivative_radialIntervalPrimitive_zero hf l b
  have he (θ : ℝ) :
      (fun x => iteratedDeriv b (fun t => radialIntervalPrimitive l f (x, t)) θ) =
        fun x => radialIntervalPrimitive l (mixedDerivative 0 b f) (x, θ) := by
    funext x
    simpa only [mixedDerivative, iteratedDeriv_zero] using congrFun hzero (x, θ)
  have hd (θ : ℝ) :
      deriv (fun x => radialIntervalPrimitive l (mixedDerivative 0 b f) (x, θ)) =
        fun x => mixedDerivative 0 b f (x, θ) := by
    funext x
    have hc : Continuous (fun t => mixedDerivative 0 b f (t, θ)) :=
      (contDiff_mixedDerivative hf 0 b).continuous.comp
        (continuous_id.prodMk continuous_const)
    exact (hc.integral_hasStrictDerivAt l x).hasDerivAt.deriv
  funext p
  change iteratedDeriv (a + 1)
      (fun x => iteratedDeriv b (fun t => radialIntervalPrimitive l f (x, t)) p.2) p.1 = _
  simp only [he, iteratedDeriv_succ', hd, mixedDerivative, iteratedDeriv_zero]

/-- The same primitive is controlled at every requested order. In
particular, the high-data bound is not inserted into an exponent. -/
theorem norm_iteratedFDeriv_radialIntervalPrimitive_le
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {l r B : ℝ} (hlr : l ≤ r) (hB : 0 ≤ B) (N : ℕ)
    (hjets : ∀ a b : ℕ, a + b ≤ N → ∀ x ∈ Icc l r, ∀ θ,
      ‖mixedDerivative a b f (x, θ)‖ ≤ B)
    (k : ℕ) (hk : k ≤ N) {p : PolarPoint} (hp : p.1 ∈ Icc l r) :
    ‖iteratedFDeriv ℝ k (radialIntervalPrimitive l f) p‖ ≤
      (2 : ℝ) ^ N * (1 + (r - l)) * B := by
  have hgap : 0 ≤ r - l := sub_nonneg.mpr hlr
  have hM : 0 ≤ (1 + (r - l)) * B := mul_nonneg (by linarith) hB
  have hb (a b : ℕ) (hab : a + b = k) :
      ‖mixedDerivative a b (radialIntervalPrimitive l f) p‖ ≤
        (1 + (r - l)) * B := by
    cases a with
    | zero =>
        rw [mixedDerivative_radialIntervalPrimitive_zero hf]
        have hbound : ‖radialIntervalPrimitive l (mixedDerivative 0 b f) p‖ ≤
            B * |p.1 - l| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro x hx
          have hx' : x ∈ Ioc l p.1 := by simpa only [uIoc_of_le hp.1] using hx
          exact hjets 0 b (hab.le.trans hk) x ⟨hx'.1.le, hx'.2.trans hp.2⟩ p.2
        calc
          _ ≤ B * |p.1 - l| := hbound
          _ = B * (p.1 - l) := by rw [abs_of_nonneg (sub_nonneg.mpr hp.1)]
          _ ≤ B * (r - l) := mul_le_mul_of_nonneg_left (by linarith only [hp.2]) hB
          _ ≤ (1 + (r - l)) * B := by nlinarith
    | succ a =>
        rw [mixedDerivative_radialIntervalPrimitive_succ hf]
        exact (hjets a b (by omega) p.1 hp p.2).trans (by nlinarith)
  calc
    _ ≤ (2 : ℝ) ^ k * ((1 + (r - l)) * B) :=
      norm_iteratedFDeriv_le_of_mixedDerivative isOpen_univ
        (contDiff_radialIntervalPrimitive hf l).contDiffOn k (mem_univ p) hM hb
    _ ≤ (2 : ℝ) ^ N * ((1 + (r - l)) * B) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hM
    _ = _ := by ring

end ContinuousFlexibility.Analysis
