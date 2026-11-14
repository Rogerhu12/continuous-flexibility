module

public import ContinuousFlexibility.Analysis.AngularSimpleDivisionBounds
public import ContinuousFlexibility.Analysis.SmoothCompactIntervalIntegral

/-!
# A genuine smooth angular Taylor quotient

The integral over a fixed interval constructs the quotient jointly in
the physical radius and angle. Its value at the removed zero is the
actual angular derivative. Applying the same construction twice gives
the quotient for a squared zero. These are definitions and exact
factorizations, not smoothness assumptions on a stored coefficient.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Interval

set_option backward.isDefEq.respectTransparency false

def angularTaylorQuotient (F : PolarPoint → ℝ) (c : ℝ) (p : PolarPoint) : ℝ :=
  ∫ t in (0 : ℝ)..1, mixedDerivative 0 1 F (p.1, t * (p.2 - c) + c)

theorem contDiff_angularTaylorQuotient
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (c : ℝ) :
    ContDiff ℝ ∞ (angularTaylorQuotient F c) := by
  have hmap : ContDiff ℝ ∞
      (fun q : PolarPoint × ℝ => (q.1.1, q.2 * (q.1.2 - c) + c)) :=
    contDiff_fst.fst.prodMk
      ((contDiff_snd.mul (contDiff_fst.snd.sub contDiff_const)).add contDiff_const)
  have h := contDiff_compact_parameterIntegral (w := fun _ : ℝ => (1 : ℝ))
    continuous_const ((contDiff_mixedDerivative hF 0 1).comp hmap)
  change ContDiff ℝ ∞ (fun p : PolarPoint =>
    ∫ t in (0 : ℝ)..1, mixedDerivative 0 1 F (p.1, t * (p.2 - c) + c))
  simpa only [one_smul, Function.comp_def] using h

theorem angularTaylorQuotient_at_center (F : PolarPoint → ℝ) (c r : ℝ) :
    angularTaylorQuotient F c (r, c) = mixedDerivative 0 1 F (r, c) := by
  simp only [angularTaylorQuotient, sub_self, mul_zero, zero_add,
    intervalIntegral.integral_const, sub_zero, one_smul]

/-- A true zero identifies the integral with an actual smooth factor,
including at the center. -/
theorem angularTaylorQuotient_factor
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (c : ℝ)
    (hzero : ∀ r : ℝ, F (r, c) = 0) (p : PolarPoint) :
    F p = (p.2 - c) * angularTaylorQuotient F c p := by
  let f : ℝ → ℝ := fun x => F (p.1, x + c)
  have hf : ContDiff ℝ ∞ f :=
    hF.comp (contDiff_const.prodMk (contDiff_id.add contDiff_const))
  have hfzero : f 0 = 0 := by
    simpa only [f, zero_add] using hzero p.1
  obtain ⟨g, hg, _, hfactor⟩ := exists_smooth_division_at_zero hf hfzero
  have hd (x : ℝ) : deriv f x = mixedDerivative 0 1 F (p.1, x + c) := by
    have h := congrFun (iteratedDeriv_comp_add_const 1 (fun θ => F (p.1, θ)) c) x
    simpa only [f, mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one] using h
  have he : g (p.2 - c) = angularTaylorQuotient F c p := by
    rw [smoothDivisionFactor_eq_integral hf hg hfactor]
    unfold angularTaylorQuotient
    apply intervalIntegral.integral_congr
    intro t _
    exact hd (t * (p.2 - c))
  have h := hfactor (p.2 - c)
  rw [he] at h
  simpa only [f, sub_add_cancel] using h

/-- The constructed quotient has the same fixed one-derivative bound
as every genuine smooth factor. -/
theorem abs_mixedDerivative_angularTaylorQuotient_le
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (c : ℝ)
    (hzero : ∀ r : ℝ, F (r, c) = 0) (a b : ℕ) {p : PolarPoint} {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |mixedDerivative a (b + 1) F (p.1, t * (p.2 - c) + c)| ≤ M) :
    |mixedDerivative a b (angularTaylorQuotient F c) p| ≤ M :=
  abs_mixedDerivative_translatedAngularFactor_le hF
    (contDiff_angularTaylorQuotient hF c) c
    (angularTaylorQuotient_factor hF c hzero) a b hbound

def squaredAngularTaylorQuotient (F : PolarPoint → ℝ) (c : ℝ) : PolarPoint → ℝ :=
  angularTaylorQuotient (angularTaylorQuotient F c) c

theorem contDiff_squaredAngularTaylorQuotient
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (c : ℝ) :
    ContDiff ℝ ∞ (squaredAngularTaylorQuotient F c) :=
  contDiff_angularTaylorQuotient (contDiff_angularTaylorQuotient hF c) c

theorem squaredAngularTaylorQuotient_factor
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (c : ℝ)
    (hzero : ∀ r : ℝ, F (r, c) = 0)
    (hfirst : ∀ r : ℝ, mixedDerivative 0 1 F (r, c) = 0) (p : PolarPoint) :
    F p = (p.2 - c) ^ 2 * squaredAngularTaylorQuotient F c p := by
  have hzero' (r : ℝ) : angularTaylorQuotient F c (r, c) = 0 := by
    rw [angularTaylorQuotient_at_center, hfirst]
  have houter := angularTaylorQuotient_factor hF c hzero p
  have hinner := angularTaylorQuotient_factor
    (contDiff_angularTaylorQuotient hF c) c hzero' p
  rw [hinner] at houter
  dsimp only [squaredAngularTaylorQuotient]
  calc
    F p = (p.2 - c) * ((p.2 - c) *
        angularTaylorQuotient (angularTaylorQuotient F c) c p) := houter
    _ = _ := by ring

theorem abs_mixedDerivative_squaredAngularTaylorQuotient_le
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (c : ℝ)
    (hzero : ∀ r : ℝ, F (r, c) = 0)
    (hfirst : ∀ r : ℝ, mixedDerivative 0 1 F (r, c) = 0)
    (a b : ℕ) {p : PolarPoint} {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |mixedDerivative a (b + 2) F (p.1, t * (p.2 - c) + c)| ≤ M) :
    |mixedDerivative a b (squaredAngularTaylorQuotient F c) p| ≤ M :=
  abs_mixedDerivative_squaredAngularFactor_le hF
    (contDiff_squaredAngularTaylorQuotient hF c) c
    (squaredAngularTaylorQuotient_factor hF c hzero hfirst) a b hbound

end ContinuousFlexibility.Analysis
