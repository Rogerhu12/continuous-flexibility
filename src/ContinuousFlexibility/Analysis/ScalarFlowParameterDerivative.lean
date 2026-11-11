import ContinuousFlexibility.Analysis.ScalarTrajectorySecant
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A genuine external-parameter derivative of a scalar flow

The two actual trajectories at different parameter values satisfy the
inhomogeneous secant equation. A second fundamental-theorem calculation
factors its forcing by the parameter increment. Joint continuity then
gives the limit of the exact difference quotient. The trajectory is
assumed continuous in the parameter, but its parameter derivative is a
conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

private theorem continuous_scalar_parameterIntegral
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H × ℝ → ℝ} (hF : Continuous F) (a b : ℝ) :
    Continuous (fun x : H => ∫ t in a..b, F (x, t)) := by
  have hc (c d : ℝ) :
      Continuous (fun x : H => ∫ t in Icc c d, F (x, t)) :=
    continuous_parametric_integral_of_continuous (μ := volume)
      (f := fun (x : H) (t : ℝ) => F (x, t)) hF isCompact_Icc
  rcases le_total a b with hab | hba
  · simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
      using hc a b
  · have hn : Continuous (fun x : H => -(∫ t in Icc b a, F (x, t))) :=
      (hc b a).neg
    simpa only [intervalIntegral.integral_of_ge hba, integral_Icc_eq_integral_Ioc]
      using hn

private theorem continuous_scalar_parameterPrimitive
    {F : ℝ × ℝ → ℝ} (hF : Continuous F) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ t in a..p.2, F (p.1, t)) := by
  have hc : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      F (q.1.1, (q.1.2 - a) * q.2 + a)) :=
    hF.comp (continuous_fst.fst.prodMk
      (((continuous_fst.snd.sub continuous_const).mul continuous_snd).add continuous_const))
  have hI := continuous_scalar_parameterIntegral hc (0 : ℝ) 1
  have hproduct : Continuous (fun p : ℝ × ℝ =>
      (p.2 - a) * ∫ t in (0 : ℝ)..1, F (p.1, (p.2 - a) * t + a)) :=
    (continuous_snd.sub continuous_const).mul hI
  have he : (fun p : ℝ × ℝ => ∫ t in a..p.2, F (p.1, t)) =
      fun p : ℝ × ℝ => (p.2 - a) *
        ∫ t in (0 : ℝ)..1, F (p.1, (p.2 - a) * t + a) := by
    funext p
    simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] using
      (intervalIntegral.smul_integral_comp_mul_add (fun t => F (p.1, t))
        (a := (0 : ℝ)) (b := 1) (p.2 - a) a).symm
  rw [he]
  exact hproduct

/-- For a continuous family with parameter-independent initial data, the
actual external-parameter derivative is the forced variational integral.
The entries of the field are parameter, time, and angular position. -/
theorem scalarFlow_hasDerivAt_parameter
    {F Dθ Dp : ℝ × (ℝ × ℝ) → ℝ} {Θ : ℝ × ℝ → ℝ} {a b c : ℝ}
    (hDθ : Continuous Dθ) (hDp : Continuous Dp)
    (hangle : ∀ p t x : ℝ,
      HasDerivAt (fun y => F (p, (t, y))) (Dθ (p, (t, x))) x)
    (hparameter : ∀ p t x : ℝ,
      HasDerivAt (fun q => F (q, (t, x))) (Dp (p, (t, x))) p)
    (hΘ : ContinuousOn Θ ((univ : Set ℝ) ×ˢ uIcc a b))
    (hinit : ∀ p : ℝ, Θ (p, a) = c)
    (hflow : ∀ p : ℝ, ∀ t ∈ uIoo a b,
      HasDerivAt (fun r => Θ (p, r)) (F (p, (t, Θ (p, t)))) t)
    (p : ℝ) :
    HasDerivAt (fun q => Θ (q, b))
      (Real.exp (∫ t in a..b, Dθ (p, (t, Θ (p, t)))) *
        ∫ t in a..b,
          Real.exp (-(∫ r in a..t, Dθ (p, (r, Θ (p, r))))) *
            Dp (p, (t, Θ (p, t)))) p := by
  let clamp : ℝ → ℝ := fun t => max (min a b) (min t (max a b))
  have hc : Continuous clamp :=
    continuous_const.max (continuous_id.min continuous_const)
  have hmem (t : ℝ) : clamp t ∈ uIcc a b :=
    ⟨le_max_left _ _, max_le min_le_max (min_le_right _ _)⟩
  have heq (t : ℝ) (ht : t ∈ uIcc a b) : clamp t = t := by
    dsimp only [clamp]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  let U : ℝ × ℝ → ℝ := fun z => Θ (z.1, clamp z.2)
  have hU : Continuous U :=
    hΘ.comp_continuous (continuous_fst.prodMk (hc.comp continuous_snd))
      (fun z => ⟨mem_univ z.1, hmem z.2⟩)
  have hUeq (q t : ℝ) (ht : t ∈ uIcc a b) : U (q, t) = Θ (q, t) := by
    dsimp only [U]
    rw [heq t ht]
  let A : ℝ × ℝ → ℝ := fun z =>
    scalarSecantAverage (fun w => Dθ (z.1, w)) (z.2, (U (p, z.2), U z))
  have hA : Continuous A := by
    have hIntegrand : Continuous (fun z : (ℝ × ℝ) × ℝ =>
        Dθ (z.1.1, (z.1.2,
          (U z.1 - U (p, z.1.2)) * z.2 + U (p, z.1.2)))) :=
      hDθ.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.prodMk
          ((((hU.comp continuous_fst).sub
            (hU.comp (continuous_const.prodMk continuous_fst.snd))).mul continuous_snd).add
              (hU.comp (continuous_const.prodMk continuous_fst.snd)))))
    exact continuous_scalar_parameterIntegral hIntegrand 0 1
  let C : ℝ × ℝ → ℝ := fun z => Dp (z.2, (z.1, U (p, z.1)))
  have hC : Continuous C :=
    hDp.comp (continuous_snd.prodMk
      (continuous_fst.prodMk (hU.comp (continuous_const.prodMk continuous_fst))))
  let B : ℝ × ℝ → ℝ := fun z => scalarSecantAverage C (z.2, (p, z.1))
  have hB : Continuous B :=
    (continuous_scalarSecantAverage hC).comp
      (continuous_snd.prodMk (continuous_const.prodMk continuous_fst))
  let I : ℝ × ℝ → ℝ := fun z => ∫ t in a..z.2, A (z.1, t)
  have hI : Continuous I := continuous_scalar_parameterPrimitive hA a
  let J : ℝ → ℝ := fun q =>
    ∫ t in a..b, Real.exp (-I (q, t)) * B (q, t)
  have hJ : Continuous J :=
    continuous_scalar_parameterIntegral ((Real.continuous_exp.comp hI.neg).mul hB) a b
  let E : ℝ → ℝ := fun q => Real.exp (I (q, b)) * J q
  have hE : Continuous E :=
    (Real.continuous_exp.comp (hI.comp (continuous_id.prodMk continuous_const))).mul hJ
  have hforcing (q t : ℝ) :
      F (q, (t, U (p, t))) - F (p, (t, U (p, t))) = B (q, t) * (q - p) :=
    scalarField_sub_eq_secant
      (F := fun z => F (z.2, (z.1, U (p, z.1)))) hC
      (fun t q => hparameter q t (U (p, t))) t p q
  have htime (q : ℝ) : ContinuousOn (fun t => Θ (q, t)) (uIcc a b) :=
    hΘ.comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨mem_univ q, ht⟩)
  have hdiff (q : ℝ) : Θ (q, b) - Θ (p, b) = (q - p) * E q := by
    have hd : ∀ t ∈ uIoo a b,
        HasDerivAt (fun r => Θ (q, r) - Θ (p, r))
          (A (q, t) * (Θ (q, t) - Θ (p, t)) + (q - p) * B (q, t)) t := by
      intro t ht
      have hclosed : t ∈ uIcc a b := uIoo_subset_uIcc_self ht
      have hs := scalarTrajectory_difference_hasDerivAt
        (hDθ.comp (continuous_const.prodMk continuous_id))
        (hangle q) (hflow q t ht) (hflow p t ht)
      apply hs.congr_deriv
      have hAe : A (q, t) =
          scalarSecantAverage (fun w => Dθ (q, w))
            (t, (Θ (p, t), Θ (q, t))) := by
        dsimp only [A]
        rw [hUeq p t hclosed, hUeq q t hclosed]
      have hb := hforcing q t
      rw [hUeq p t hclosed] at hb
      dsimp only
      rw [← hAe, hb]
      ring
    have hz : Θ (q, a) - Θ (p, a) = 0 := by rw [hinit, hinit, sub_self]
    have hAq : Continuous (fun t => A (q, t)) :=
      hA.comp (continuous_const.prodMk continuous_id)
    have hBq : Continuous (fun t => (q - p) * B (q, t)) :=
      continuous_const.mul (hB.comp (continuous_const.prodMk continuous_id))
    have hsol := scalar_forced_linearODE_zero_initial hAq hBq
      ((htime q).sub (htime p)) hd hz
    have hfactor :
        (∫ t in a..b, Real.exp (-I (q, t)) * ((q - p) * B (q, t))) =
          (q - p) * J q := by
      dsimp only [J]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      ring
    change Θ (q, b) - Θ (p, b) =
      Real.exp (I (q, b)) *
        (∫ t in a..b, Real.exp (-I (q, t)) * ((q - p) * B (q, t))) at hsol
    rw [hfactor] at hsol
    dsimp only [E]
    rw [hsol]
    ring
  have hslope : slope (fun q => Θ (q, b)) p =ᶠ[𝓝[≠] p] E := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [slope_def_field]
    dsimp only
    rw [hdiff q]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hq)
  have hparam : HasDerivAt (fun q => Θ (q, b)) (E p) p :=
    hasDerivAt_iff_tendsto_slope.mpr
      ((tendsto_congr' hslope).mpr (hE.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  have hIdiag (t : ℝ) (ht : t ∈ uIcc a b) :
      I (p, t) = ∫ r in a..t, Dθ (p, (r, Θ (p, r))) := by
    dsimp only [I]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only [A]
    rw [scalarSecantAverage_diagonal, hUeq p r (uIcc_subset_uIcc_left ht hr)]
  have hJdiag : J p =
      ∫ t in a..b, Real.exp (-(∫ r in a..t, Dθ (p, (r, Θ (p, r))))) *
        Dp (p, (t, Θ (p, t))) := by
    dsimp only [J]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hIdiag t ht]
    dsimp only [B]
    rw [scalarSecantAverage_diagonal]
    dsimp only [C]
    rw [hUeq p t ht]
  simpa only [E, hIdiag b right_mem_uIcc, hJdiag] using hparam

end ContinuousFlexibility.Analysis
