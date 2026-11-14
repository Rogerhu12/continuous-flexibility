module

public import ContinuousFlexibility.Analysis.ScalarTrajectorySecant
public import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Actual parameter derivatives of a scalar flow

Finite differences of the field and of the initial data are represented
by integrals of their actual Fréchet derivatives. The exact forced
trajectory equation then gives a continuous operator-valued secant.
Its norm remainder proves the Fréchet derivative of the chosen flow,
without assuming any parameter differentiability of that flow.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

section NormedParameter

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The fundamental theorem along an affine segment gives an actual
operator-valued secant for a scalar function. -/
theorem scalar_sub_eq_integral_fderiv
    {f : P → ℝ} {D : P → P →L[ℝ] ℝ}
    (hD : Continuous D) (hf : ∀ x : P, HasFDerivAt f (D x) x) (p q : P) :
    f q - f p = (∫ s in (0 : ℝ)..1, D (s • (q - p) + p)) (q - p) := by
  have hpath (s : ℝ) :
      HasDerivAt (fun r : ℝ => r • (q - p) + p) (q - p) s := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const (q - p)).add_const p
  have hd (s : ℝ) :
      HasDerivAt (fun r : ℝ => f (r • (q - p) + p))
        (D (s • (q - p) + p) (q - p)) s :=
    (hf (s • (q - p) + p)).comp_hasDerivAt s (hpath s)
  have hc : Continuous (fun s : ℝ => D (s • (q - p) + p)) :=
    hD.comp ((continuous_id.smul continuous_const).add continuous_const)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) ((hc.clm_apply continuous_const).intervalIntegrable 0 1)
  calc
    f q - f p = ∫ s in (0 : ℝ)..1, D (s • (q - p) + p) (q - p) := by
      simpa only [one_smul, zero_smul, zero_add, sub_add_cancel] using hFTC.symm
    _ = (∫ s in (0 : ℝ)..1, D (s • (q - p) + p)) (q - p) :=
      (ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1) (q - p)).symm

/-- A continuous operator-valued secant gives the genuine Fréchet
derivative. The estimate uses the operator norm of its difference. -/
theorem hasFDerivAt_of_continuous_secantCLM
    {f : P → ℝ} {E : P → P →L[ℝ] ℝ} {p : P}
    (hE : ContinuousAt E p)
    (hfactor : ∀ q : P, f q - f p = E q (q - p)) :
    HasFDerivAt f (E p) p := by
  apply hasFDerivAt_iff_tendsto.mpr
  have hlim : Tendsto (fun q => ‖E q - E p‖) (𝓝 p) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun _ : P => E p) p := continuousAt_const
    simpa only [Pi.sub_apply, sub_self, norm_zero] using (hE.sub hc).norm.tendsto
  apply squeeze_zero (fun q => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun q => ?_) hlim
  change ‖q - p‖⁻¹ * ‖f q - f p - E p (q - p)‖ ≤ ‖E q - E p‖
  rw [hfactor q]
  by_cases hq : q = p
  · subst q
    simp only [sub_self, map_zero, norm_zero,
      inv_zero, zero_mul, le_refl]
  · have hn : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
    rw [← ContinuousLinearMap.sub_apply]
    calc
      ‖q - p‖⁻¹ * ‖(E q - E p) (q - p)‖ ≤
          ‖q - p‖⁻¹ * (‖E q - E p‖ * ‖q - p‖) :=
        mul_le_mul_of_nonneg_left ((E q - E p).le_opNorm (q - p))
          (inv_nonneg.mpr hn.le)
      _ = ‖E q - E p‖ := by
        rw [mul_comm ‖E q - E p‖ ‖q - p‖, ← mul_assoc,
          inv_mul_cancel₀ hn.ne', one_mul]

end NormedParameter

section FiniteDimensionalParameter

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- The external-parameter derivative of the actual chosen scalar flow.
The initial value may vary smoothly with the same parameter. -/
theorem scalarFlow_hasFDerivAt_parameter
    {F Dθ : P × (ℝ × ℝ) → ℝ}
    {Dp : P × (ℝ × ℝ) → P →L[ℝ] ℝ}
    {Θ : P × ℝ → ℝ} {v : P → ℝ} {Dv : P → P →L[ℝ] ℝ} {a b : ℝ}
    (hDθ : Continuous Dθ) (hDp : Continuous Dp) (hDv : Continuous Dv)
    (hangle : ∀ p : P, ∀ t x : ℝ,
      HasDerivAt (fun y => F (p, (t, y))) (Dθ (p, (t, x))) x)
    (hparameter : ∀ p : P, ∀ t x : ℝ,
      HasFDerivAt (fun q => F (q, (t, x))) (Dp (p, (t, x))) p)
    (hvalue : ∀ p : P, HasFDerivAt v (Dv p) p)
    (hΘ : ContinuousOn Θ ((univ : Set P) ×ˢ uIcc a b))
    (hinit : ∀ p : P, Θ (p, a) = v p)
    (hflow : ∀ p : P, ∀ t ∈ uIoo a b,
      HasDerivAt (fun r => Θ (p, r)) (F (p, (t, Θ (p, t)))) t)
    (p : P) :
    HasFDerivAt (fun q => Θ (q, b))
      (Real.exp (∫ t in a..b, Dθ (p, (t, Θ (p, t)))) •
        (Dv p + ∫ t in a..b,
          Real.exp (-(∫ r in a..t, Dθ (p, (r, Θ (p, r))))) •
            Dp (p, (t, Θ (p, t))))) p := by
  let clamp : ℝ → ℝ := fun t => max (min a b) (min t (max a b))
  have hc : Continuous clamp :=
    continuous_const.max (continuous_id.min continuous_const)
  have hmem (t : ℝ) : clamp t ∈ uIcc a b :=
    ⟨le_max_left _ _, max_le min_le_max (min_le_right _ _)⟩
  have heq (t : ℝ) (ht : t ∈ uIcc a b) : clamp t = t := by
    dsimp only [clamp]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  let U : P × ℝ → ℝ := fun z => Θ (z.1, clamp z.2)
  have hU : Continuous U :=
    hΘ.comp_continuous (continuous_fst.prodMk (hc.comp continuous_snd))
      (fun z => ⟨mem_univ z.1, hmem z.2⟩)
  have hUeq (q : P) (t : ℝ) (ht : t ∈ uIcc a b) : U (q, t) = Θ (q, t) := by
    dsimp only [U]
    rw [heq t ht]
  let A : P × ℝ → ℝ := fun z =>
    scalarSecantAverage (fun w => Dθ (z.1, w)) (z.2, (U (p, z.2), U z))
  have hA : Continuous A := by
    have hIntegrand : Continuous (fun z : (P × ℝ) × ℝ =>
        Dθ (z.1.1, (z.1.2,
          (U z.1 - U (p, z.1.2)) * z.2 + U (p, z.1.2)))) :=
      hDθ.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.prodMk
          ((((hU.comp continuous_fst).sub
            (hU.comp (continuous_const.prodMk continuous_fst.snd))).mul continuous_snd).add
              (hU.comp (continuous_const.prodMk continuous_fst.snd)))))
    exact continuous_parametric_intervalIntegral hIntegrand 0 1
  let B : P × ℝ → P →L[ℝ] ℝ := fun z =>
    ∫ s in (0 : ℝ)..1, Dp (s • (z.1 - p) + p, (z.2, U (p, z.2)))
  have hB : Continuous B := by
    have hIntegrand : Continuous (fun z : (P × ℝ) × ℝ =>
        Dp (z.2 • (z.1.1 - p) + p, (z.1.2, U (p, z.1.2)))) :=
      hDp.comp
        (((continuous_snd.smul (continuous_fst.fst.sub continuous_const)).add
          continuous_const).prodMk
            (continuous_fst.snd.prodMk
              (hU.comp (continuous_const.prodMk continuous_fst.snd))))
    exact continuous_parametric_intervalIntegral hIntegrand 0 1
  let V : P → P →L[ℝ] ℝ := fun q => ∫ s in (0 : ℝ)..1, Dv (s • (q - p) + p)
  have hVIntegrand : Continuous (fun z : P × ℝ => Dv (z.2 • (z.1 - p) + p)) :=
    hDv.comp ((continuous_snd.smul (continuous_fst.sub continuous_const)).add
      continuous_const)
  have hV : Continuous V := continuous_parametric_intervalIntegral hVIntegrand 0 1
  let I : P × ℝ → ℝ := fun z => ∫ t in a..z.2, A (z.1, t)
  have hI : Continuous I :=
    (contDiff_parametric_primitive_nat (n := 0) (contDiff_zero.mpr hA) a).continuous
  let J : P → P →L[ℝ] ℝ := fun q =>
    ∫ t in a..b, Real.exp (-I (q, t)) • B (q, t)
  have hJI : Continuous (fun z : P × ℝ => Real.exp (-I z) • B z) :=
    (Real.continuous_exp.comp hI.neg).smul hB
  have hJ : Continuous J := continuous_parametric_intervalIntegral hJI a b
  let E : P → P →L[ℝ] ℝ := fun q => Real.exp (I (q, b)) • (V q + J q)
  have hE : Continuous E :=
    (Real.continuous_exp.comp (hI.comp (continuous_id.prodMk continuous_const))).smul
      (hV.add hJ)
  have hforcing (q : P) (t : ℝ) :
      F (q, (t, U (p, t))) - F (p, (t, U (p, t))) = B (q, t) (q - p) :=
    scalar_sub_eq_integral_fderiv
      (f := fun q : P => F (q, (t, U (p, t))))
      (D := fun q : P => Dp (q, (t, U (p, t))))
      (hDp.comp (continuous_id.prodMk continuous_const))
      (fun q => hparameter q t (U (p, t))) p q
  have hvalue_diff (q : P) : v q - v p = V q (q - p) :=
    scalar_sub_eq_integral_fderiv hDv hvalue p q
  have htime (q : P) : ContinuousOn (fun t => Θ (q, t)) (uIcc a b) :=
    hΘ.comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨mem_univ q, ht⟩)
  have hdiff (q : P) : Θ (q, b) - Θ (p, b) = E q (q - p) := by
    have hd : ∀ t ∈ uIoo a b,
        HasDerivAt (fun r => Θ (q, r) - Θ (p, r))
          (A (q, t) * (Θ (q, t) - Θ (p, t)) + B (q, t) (q - p)) t := by
      intro t ht
      have hclosed : t ∈ uIcc a b := uIoo_subset_uIcc_self ht
      have hs := scalarTrajectory_difference_hasDerivAt
        (F₁ := fun w : ℝ × ℝ => F (q, w))
        (F₀ := fun w : ℝ × ℝ => F (p, w))
        (D₁ := fun w : ℝ × ℝ => Dθ (q, w))
        (u₁ := fun r => Θ (q, r)) (u₀ := fun r => Θ (p, r)) (t := t)
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
      exact congrArg₂ (fun c d : ℝ => c * (Θ (q, t) - Θ (p, t)) + d) hAe.symm hb
    have hAq : Continuous (fun t => A (q, t)) :=
      hA.comp (continuous_const.prodMk continuous_id)
    have hBq : Continuous (fun t => B (q, t) (q - p)) :=
      (hB.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
    have hsol := scalar_forced_linearODE_eq hAq hBq ((htime q).sub (htime p)) hd
    have hJapply : J q (q - p) =
        ∫ t in a..b, Real.exp (-I (q, t)) * B (q, t) (q - p) := by
      have hJq : Continuous (fun t : ℝ => Real.exp (-I (q, t)) • B (q, t)) :=
        hJI.comp (continuous_const.prodMk continuous_id)
      dsimp only [J]
      rw [ContinuousLinearMap.intervalIntegral_apply
        (μ := volume) (hJq.intervalIntegrable a b) (q - p)]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hEapply : E q (q - p) =
        Real.exp (I (q, b)) * (V q (q - p) + J q (q - p)) := by
      dsimp only [E]
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    change Θ (q, b) - Θ (p, b) = Real.exp (I (q, b)) *
      (Θ (q, a) - Θ (p, a) +
        ∫ t in a..b, Real.exp (-I (q, t)) * B (q, t) (q - p)) at hsol
    rw [hinit q, hinit p, hvalue_diff q, ← hJapply] at hsol
    exact hsol.trans hEapply.symm
  have hparam : HasFDerivAt (fun q => Θ (q, b)) (E p) p :=
    hasFDerivAt_of_continuous_secantCLM hE.continuousAt hdiff
  have hVdiag : V p = Dv p := by
    simp only [V, sub_self, smul_zero, zero_add,
      intervalIntegral.integral_const, sub_zero, one_smul]
  have hIdiag (t : ℝ) (ht : t ∈ uIcc a b) :
      I (p, t) = ∫ r in a..t, Dθ (p, (r, Θ (p, r))) := by
    dsimp only [I]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only [A]
    rw [scalarSecantAverage_diagonal, hUeq p r (uIcc_subset_uIcc_left ht hr)]
  have hJdiag : J p =
      ∫ t in a..b, Real.exp (-(∫ r in a..t, Dθ (p, (r, Θ (p, r))))) •
        Dp (p, (t, Θ (p, t))) := by
    dsimp only [J]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hIdiag t ht]
    simp only [B, sub_self, smul_zero, zero_add,
      intervalIntegral.integral_const, sub_zero, one_smul, hUeq p t ht]
  simpa only [E, hVdiag, hIdiag b right_mem_uIcc, hJdiag] using hparam

end FiniteDimensionalParameter
end ContinuousFlexibility.Analysis
