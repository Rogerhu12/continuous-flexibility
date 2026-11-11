import ContinuousFlexibility.Analysis.CharacteristicODEUniqueness
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The angular variational equation for a scalar flow

The difference of two trajectories solves a scalar linear equation whose
coefficient is the average of the actual angular derivative of the vector
field between them.  The exponential solution formula and continuity of
parametric integrals then give the first angular derivative of the flow.
The radial dependence of the vector field is only required to be continuous.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem scalar_linear_ode_eq_exp_integral
    {a b : ℝ} {α f : ℝ → ℝ} (hab : a < b) (hα : Continuous α)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (α t * f t) t) :
    ∀ t ∈ Icc a b, f t = f a * Real.exp (∫ s in a..t, α s) := by
  let g : ℝ → ℝ := fun t => f a * Real.exp (∫ s in a..t, α s)
  have hg' (t : ℝ) : HasDerivAt g (α t * g t) t := by
    have h := (((hα.integral_hasStrictDerivAt a t).hasDerivAt.exp).const_mul (f a))
    have he : f a * (Real.exp (∫ s in a..t, α s) * α t) = α t * g t := by
      dsimp only [g]
      ring
    exact (h.congr_deriv he).congr_of_eventuallyEq
      (Eventually.of_forall fun s => by simp only [g, Pi.mul_apply])
  have hg : ContinuousOn g (Icc a b) :=
    (show Differentiable ℝ g from fun t => (hg' t).differentiableAt).continuous.continuousOn
  refine ode_solution_unique_of_continuous_angular_derivative
    (v := fun t y => α t * y) (d := fun p => α p.1) hab
    (((hα.comp continuous_fst).mul continuous_snd).continuousOn) ?_
    (hα.comp continuous_fst).continuousOn hf hf' hg (fun t _ => hg' t) ?_
  · intro t _ θ
    have h := ((hasDerivAt_id θ).const_mul (α t)).congr_deriv
      (g' := α t) (by ring)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp only [id_eq])
  · simp only [g, intervalIntegral.integral_same, Real.exp_zero, mul_one]

/-- The finite angular difference is its displacement times the integral
of the actual derivative along the segment. -/
theorem difference_eq_mul_integral_derivative
    {f d : ℝ → ℝ} (hf : ∀ θ, HasDerivAt f (d θ) θ)
    (hd : Continuous d) (x y : ℝ) :
    f y - f x = (y - x) * ∫ u in (0 : ℝ)..1, d (x + u * (y - x)) := by
  have hderiv (u : ℝ) : HasDerivAt (fun t : ℝ => f (x + t * (y - x)))
      ((y - x) * d (x + u * (y - x))) u := by
    have h := (hf (x + u * (y - x))).comp u
      ((hasDerivAt_const u x).add ((hasDerivAt_id u).mul_const (y - x)))
    have he : d (x + u * (y - x)) * (0 + 1 * (y - x)) =
        (y - x) * d (x + u * (y - x)) := by ring
    exact (h.congr_deriv he).congr_of_eventuallyEq
      (Eventually.of_forall fun t => by simp only [Function.comp_def, Pi.add_apply, id_eq])
  have hc : Continuous (fun u : ℝ => (y - x) * d (x + u * (y - x))) :=
    continuous_const.mul (hd.comp (continuous_const.add (continuous_id.mul_const _)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (_ : u ∈ uIcc (0 : ℝ) 1) => hderiv u) (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hFTC
  simpa using hFTC.symm

/-- An actual scalar flow of a vector field with a continuous angular
derivative satisfies the first variational formula.  Joint continuity of
the flow suffices; its angular differentiability is a conclusion. -/
theorem scalar_flow_hasDerivAt_exp_integral
    {a b : ℝ} {v d F : ℝ → ℝ → ℝ} (hab : a < b)
    (hd : Continuous (fun p : PolarPoint => d p.1 p.2))
    (hvd : ∀ t θ, HasDerivAt (v t) (d t θ) θ)
    (hF : Continuous (fun p : PolarPoint => F p.1 p.2))
    (hinit : ∀ θ, F a θ = θ)
    (hode : ∀ θ t, t ∈ Ioo a b → HasDerivAt (fun s => F s θ) (v t (F t θ)) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (F t) (Real.exp (∫ s in a..t, d s (F s θ))) θ := by
  let A : ℝ → ℝ → ℝ := fun h s =>
    ∫ u in (0 : ℝ)..1, d s (F s θ + u * (F s (θ + h) - F s θ))
  have hA : Continuous (fun p : PolarPoint => A p.1 p.2) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun p : PolarPoint => fun u =>
        d p.2 (F p.2 θ + u * (F p.2 (θ + p.1) - F p.2 θ))) ?_ 0 1
    have hs : Continuous (fun p : PolarPoint × ℝ => p.1.2) := continuous_fst.snd
    have hh : Continuous (fun p : PolarPoint × ℝ => p.1.1) := continuous_fst.fst
    have hu : Continuous (fun p : PolarPoint × ℝ => p.2) := continuous_snd
    apply hd.comp
    exact hs.prodMk
      ((hF.comp (hs.prodMk continuous_const)).add
        (hu.mul
          ((hF.comp (hs.prodMk (continuous_const.add hh))).sub
            (hF.comp (hs.prodMk continuous_const)))))
  have hA0 (s : ℝ) : A 0 s = d s (F s θ) := by
    simp only [A, add_zero, sub_self, mul_zero, add_zero, intervalIntegral.integral_const,
      sub_zero, one_smul]
  have hdiff (h : ℝ) :
      F t (θ + h) - F t θ = h * Real.exp (∫ s in a..t, A h s) := by
    have hA_h : Continuous (A h) := hA.comp (continuous_const.prodMk continuous_id)
    have hcurve : ContinuousOn (fun s => F s (θ + h) - F s θ) (Icc a b) :=
      ((hF.comp (continuous_id.prodMk continuous_const)).sub
        (hF.comp (continuous_id.prodMk continuous_const))).continuousOn
    have hcurve' : ∀ s ∈ Ioo a b,
        HasDerivAt (fun r => F r (θ + h) - F r θ)
          (A h s * (F s (θ + h) - F s θ)) s := by
      intro s hs
      have he := difference_eq_mul_integral_derivative (hvd s)
        (hd.comp (continuous_const.prodMk continuous_id)) (F s θ) (F s (θ + h))
      have hder := ((hode (θ + h) s hs).sub (hode θ s hs)).congr_deriv
        (g' := A h s * (F s (θ + h) - F s θ)) (by
          rw [he]
          exact mul_comm _ _)
      exact hder.congr_of_eventuallyEq
        (Eventually.of_forall fun r => by simp only [Pi.sub_apply])
    have he := scalar_linear_ode_eq_exp_integral hab hA_h hcurve hcurve' t ht
    simpa only [hinit, add_sub_cancel_left] using he
  have hlim : Tendsto (fun h => Real.exp (∫ s in a..t, A h s)) (𝓝[≠] (0 : ℝ))
      (𝓝 (Real.exp (∫ s in a..t, d s (F s θ)))) := by
    have hc := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hA a t).exp
    simpa only [hA0] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hh
  rw [hdiff h]
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hh0, one_mul]

/-- Extend a scalar field continuously from a closed radial strip by
clamping only its radial coordinate. -/
def closedStripExtend {a b : ℝ} (hab : a ≤ b) (F : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  F (projIcc a b hab p.1, p.2)

theorem closedStripExtend_eq {a b : ℝ} (hab : a ≤ b) (F : PolarPoint → ℝ)
    {p : PolarPoint} (hp : p.1 ∈ Icc a b) : closedStripExtend hab F p = F p := by
  simp only [closedStripExtend, projIcc_of_mem hab hp]

theorem continuous_closedStripExtend {a b : ℝ} (hab : a ≤ b) {F : PolarPoint → ℝ}
    (hF : ContinuousOn F (Icc a b ×ˢ (univ : Set ℝ))) :
    Continuous (closedStripExtend hab F) := by
  have hρ : Continuous (fun p : PolarPoint => ((projIcc a b hab p.1 : ℝ), p.2)) :=
    ((continuous_subtype_val.comp continuous_projIcc).comp continuous_fst).prodMk continuous_snd
  exact (hF.comp_continuous hρ (fun p => ⟨(projIcc a b hab p.1).property, mem_univ _⟩)).congr
    fun p => rfl

/-- The variational formula on a closed radial strip, including both
turning radii.  The ODE itself is required only on the open interval. -/
theorem scalar_flow_hasDerivAt_exp_integral_on
    {a b : ℝ} {v d F : ℝ → ℝ → ℝ} (hab : a < b)
    (hd : ContinuousOn (fun p : PolarPoint => d p.1 p.2) (Icc a b ×ˢ univ))
    (hvd : ∀ t ∈ Icc a b, ∀ θ, HasDerivAt (v t) (d t θ) θ)
    (hF : ContinuousOn (fun p : PolarPoint => F p.1 p.2) (Icc a b ×ˢ univ))
    (hinit : ∀ θ, F a θ = θ)
    (hode : ∀ θ t, t ∈ Ioo a b → HasDerivAt (fun s => F s θ) (v t (F t θ)) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (F t) (Real.exp (∫ s in a..t, d s (F s θ))) θ := by
  let ve : ℝ → ℝ → ℝ := fun r x => closedStripExtend hab.le (fun p => v p.1 p.2) (r, x)
  let de : ℝ → ℝ → ℝ := fun r x => closedStripExtend hab.le (fun p => d p.1 p.2) (r, x)
  let Fe : ℝ → ℝ → ℝ := fun r x => closedStripExtend hab.le (fun p => F p.1 p.2) (r, x)
  have hde : Continuous (fun p : PolarPoint => de p.1 p.2) :=
    continuous_closedStripExtend hab.le hd
  have hFe : Continuous (fun p : PolarPoint => Fe p.1 p.2) :=
    continuous_closedStripExtend hab.le hF
  have hved (r x : ℝ) : HasDerivAt (ve r) (de r x) x :=
    hvd (projIcc a b hab.le r) (projIcc a b hab.le r).property x
  have hFeinit (x : ℝ) : Fe a x = x := by
    rw [show Fe a x = F a x from closedStripExtend_eq hab.le _ (left_mem_Icc.mpr hab.le)]
    exact hinit x
  have hFeode : ∀ x r, r ∈ Ioo a b →
      HasDerivAt (fun s => Fe s x) (ve r (Fe r x)) r := by
    intro x r hr
    have hpoint : ve r (Fe r x) = v r (F r x) := by
      simp only [ve, Fe, closedStripExtend, projIcc_of_mem hab.le ⟨hr.1.le, hr.2.le⟩]
    have heq : (fun s => Fe s x) =ᶠ[𝓝 r] (fun s => F s x) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
      exact closedStripExtend_eq hab.le _ ⟨hs.1.le, hs.2.le⟩
    exact ((hode x r hr).congr_deriv hpoint.symm).congr_of_eventuallyEq heq
  have h := scalar_flow_hasDerivAt_exp_integral hab hde hved hFe hFeinit hFeode ht θ
  have hint : (∫ s in a..t, de s (Fe s θ)) = ∫ s in a..t, d s (F s θ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    simp only [de, Fe, closedStripExtend, projIcc_of_mem hab.le hs']
  exact (h.congr_deriv (congrArg Real.exp hint)).congr_of_eventuallyEq
    (Eventually.of_forall fun x => (closedStripExtend_eq hab.le _ ht).symm)

/-- The first angular derivative furnished by the variational equation is
jointly continuous, including at the initial and terminal radii. -/
theorem scalar_flow_angular_deriv_continuousOn
    {a b : ℝ} {v d F : ℝ → ℝ → ℝ} (hab : a < b)
    (hd : ContinuousOn (fun p : PolarPoint => d p.1 p.2) (Icc a b ×ˢ univ))
    (hvd : ∀ t ∈ Icc a b, ∀ θ, HasDerivAt (v t) (d t θ) θ)
    (hF : ContinuousOn (fun p : PolarPoint => F p.1 p.2) (Icc a b ×ˢ univ))
    (hinit : ∀ θ, F a θ = θ)
    (hode : ∀ θ t, t ∈ Ioo a b → HasDerivAt (fun s => F s θ) (v t (F t θ)) t) :
    ContinuousOn (fun p : PolarPoint => deriv (F p.1) p.2) (Icc a b ×ˢ univ) := by
  let de := closedStripExtend hab.le (fun p : PolarPoint => d p.1 p.2)
  let Fe := closedStripExtend hab.le (fun p : PolarPoint => F p.1 p.2)
  have hde : Continuous de := continuous_closedStripExtend hab.le hd
  have hFe : Continuous Fe := continuous_closedStripExtend hab.le hF
  have hi : Continuous (fun p : PolarPoint × ℝ => de (p.2, Fe (p.2, p.1.2))) :=
    hde.comp (continuous_snd.prodMk (hFe.comp (continuous_snd.prodMk continuous_fst.snd)))
  have hc : Continuous (fun p : PolarPoint =>
      Real.exp (∫ s in a..p.1, de (s, Fe (s, p.2)))) :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun p : PolarPoint => fun s => de (s, Fe (s, p.2))) hi continuous_fst).exp
  apply hc.continuousOn.congr
  intro p hp
  have h := (scalar_flow_hasDerivAt_exp_integral_on hab hd hvd hF hinit hode hp.1 p.2).deriv
  have hint : (∫ s in a..p.1, de (s, Fe (s, p.2))) =
      ∫ s in a..p.1, d s (F s p.2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hp.1.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans hp.1.2⟩
    simp only [de, Fe, closedStripExtend, projIcc_of_mem hab.le hs']
  exact h.trans (congrArg Real.exp hint.symm)

theorem scalar_flow_angular_contDiff_one
    {a b : ℝ} {v d F : ℝ → ℝ → ℝ} (hab : a < b)
    (hd : ContinuousOn (fun p : PolarPoint => d p.1 p.2) (Icc a b ×ˢ univ))
    (hvd : ∀ t ∈ Icc a b, ∀ θ, HasDerivAt (v t) (d t θ) θ)
    (hF : ContinuousOn (fun p : PolarPoint => F p.1 p.2) (Icc a b ×ˢ univ))
    (hinit : ∀ θ, F a θ = θ)
    (hode : ∀ θ t, t ∈ Ioo a b → HasDerivAt (fun s => F s θ) (v t (F t θ)) t)
    {t : ℝ} (ht : t ∈ Icc a b) : ContDiff ℝ 1 (F t) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun θ => (scalar_flow_hasDerivAt_exp_integral_on hab hd hvd hF hinit hode ht θ).differentiableAt, ?_⟩
  have hdc := scalar_flow_angular_deriv_continuousOn hab hd hvd hF hinit hode
  exact (hdc.comp_continuous (continuous_const.prodMk continuous_id)
    (fun θ => ⟨ht, mem_univ _⟩)).congr fun θ => rfl

end ContinuousFlexibility.Analysis
