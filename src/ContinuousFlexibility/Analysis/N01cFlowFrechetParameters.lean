import ContinuousFlexibility.Analysis.N01cFlowParameterSmooth

/-!
# Genuine Fréchet regularity in finite-dimensional speed parameters

The actual scalar-parameter variation theorem is applied to every affine
parameter line.  Its values are evaluations of one continuous linear map:
the inhomogeneous variational integral of the genuine speed derivative.
A separate fundamental-theorem argument turns these actual line
derivatives into a Fréchet derivative.  The two coordinate derivatives,
in parameter and time, then bootstrap all finite joint orders.

The global theorem assumes continuity of the supplied trajectory family,
not any of its parameter derivatives.  The compact time-change theorem
retains this explicit continuity hypothesis; no existence or parameter
regularity of a trajectory family is encoded in the speed assumptions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Asymptotics
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A continuous linear secant factor gives the genuine Fréchet derivative. -/
theorem hasFDerivAt_of_continuous_linear_secant
    {f : E → ℝ} {R : E → E →L[ℝ] ℝ} {x : E}
    (hR : ContinuousAt R x)
    (hfactor : ∀ y : E, f y - f x = R y (y - x)) :
    HasFDerivAt f (R x) x := by
  apply hasFDerivAt_iff_isLittleO.mpr
  rw [isLittleO_iff]
  intro ε hε
  have hn : Tendsto (fun y => ‖R y - R x‖) (𝓝 x) (𝓝 (0 : ℝ)) := by
    have hsub : ContinuousAt (fun y : E => R y - R x) x :=
      hR.sub continuousAt_const
    simpa only [sub_self, norm_zero] using hsub.norm.tendsto
  filter_upwards [hn.eventually (gt_mem_nhds hε)] with y hy
  calc
    ‖f y - f x - R x (y - x)‖ = ‖(R y - R x) (y - x)‖ := by
      rw [hfactor y, ContinuousLinearMap.sub_apply]
    _ ≤ ‖R y - R x‖ * ‖y - x‖ := (R y - R x).le_opNorm _
    _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hy.le (norm_nonneg _)

/-- Continuous linear candidate derivatives and genuine derivatives on
all affine lines give actual Fréchet differentiability, by integration
along the segment between the two parameter values. -/
theorem hasFDerivAt_of_continuous_affine_line_derivatives
    {f : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hD : Continuous D)
    (hline : ∀ q v : E, ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => f (q + r • v)) (D (q + s • v) v) s)
    (x : E) : HasFDerivAt f (D x) x := by
  let R : E → E →L[ℝ] ℝ := fun y => ∫ s in (0 : ℝ)..1, D (x + s • (y - x))
  have hR : Continuous R :=
    continuous_parametric_intervalIntegral
      (hD.comp (continuous_const.add
        (continuous_snd.smul (continuous_fst.sub continuous_const)))) 0 1
  have hfactor (y : E) : f y - f x = R y (y - x) := by
    have hc : Continuous (fun s : ℝ => D (x + s • (y - x))) :=
      hD.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hline x (y - x) s)
      ((hc.clm_apply continuous_const).intervalIntegrable 0 1)
    dsimp only [R]
    rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1)]
    simpa using hd.symm
  have hd := hasFDerivAt_of_continuous_linear_secant hR.continuousAt hfactor
  simpa only [R, sub_self, smul_zero, add_zero,
    intervalIntegral.integral_const, sub_zero, one_smul] using hd

/-- The true speed derivative in its vector parameter. -/
def circleVectorSpeedParameterDeriv (G : E × PolarPoint → ℝ)
    (p : E × PolarPoint) : E →L[ℝ] ℝ :=
  (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E PolarPoint)

/-- The true angular speed derivative, retaining all vector parameters. -/
def circleVectorSpeedAngleDeriv (G : E × PolarPoint → ℝ) (p : E × PolarPoint) : ℝ :=
  fderiv ℝ G p (0, (0, 1))

theorem contDiff_circleVectorSpeedParameterDeriv {G : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (circleVectorSpeedParameterDeriv G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

theorem contDiff_circleVectorSpeedAngleDeriv {G : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (circleVectorSpeedAngleDeriv G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem circleVectorSpeedAngleDeriv_eq_angularPartial {G : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (q : E) (p : PolarPoint) :
    circleVectorSpeedAngleDeriv G (q, p) = angularPartial (fun x => G (q, x)) p := by
  have hs : HasFDerivAt (fun x : PolarPoint => G (q, x))
      ((fderiv ℝ G (q, p)).comp (ContinuousLinearMap.inr ℝ E PolarPoint)) p :=
    (hG.differentiable (by simp) (q, p)).hasFDerivAt.comp p
      (hasFDerivAt_prodMk_right q p)
  change fderiv ℝ G (q, p) (0, (0, 1)) =
    fderiv ℝ (fun x : PolarPoint => G (q, x)) p (0, 1)
  rw [hs.fderiv]
  rfl

/-- The actual speed restricted to an affine vector-parameter line. -/
def circleVectorSpeedLine (G : E × PolarPoint → ℝ) (q v : E)
    (p : ℝ × PolarPoint) : ℝ := G (q + p.1 • v, p.2)

theorem contDiff_circleVectorSpeedLine {G : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (q v : E) : ContDiff ℝ ∞ (circleVectorSpeedLine G q v) :=
  hG.comp ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd)

theorem circleVectorSpeedLine_parameterDeriv {G : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (q v : E) (s : ℝ) (p : PolarPoint) :
    circleSpeedParameterDeriv (circleVectorSpeedLine G q v) (s, p) =
      circleVectorSpeedParameterDeriv G (q + s • v, p) v := by
  apply (hasDerivAt_circleSpeed_parameterSlice
    (contDiff_circleVectorSpeedLine hG q v) s p).unique
  have hs : HasDerivAt (fun r : ℝ => q + r • v) v s := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const v).const_add q
  exact (hG.differentiable (by simp) (q + s • v, p)).hasFDerivAt.comp_hasDerivAt s
    (hs.prodMk (hasDerivAt_const s p))

theorem circleVectorSpeedLine_angleDeriv {G : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (q v : E) (s : ℝ) (p : PolarPoint) :
    circleSpeedAngleDeriv (circleVectorSpeedLine G q v) (s, p) =
      circleVectorSpeedAngleDeriv G (q + s • v, p) := by
  rw [circleSpeedAngleDeriv_eq_angularPartial (contDiff_circleVectorSpeedLine hG q v)]
  exact (circleVectorSpeedAngleDeriv_eq_angularPartial hG (q + s • v) p).symm

/-- A continuous linear map built from the actual variational integral.
Its linearity is in the vector parameter direction, not an assumed
property of a trajectory derivative. -/
def circleVectorTrajectoryParameterDerivative (G : E × PolarPoint → ℝ)
    (Θ : E × ℝ → ℝ) (p : E × ℝ) : E →L[ℝ] ℝ :=
  Real.exp (∫ r in (0 : ℝ)..p.2,
    circleVectorSpeedAngleDeriv G (p.1, (r, Θ (p.1, r)))) •
      ∫ t in (0 : ℝ)..p.2,
        Real.exp (-(∫ r in (0 : ℝ)..t,
          circleVectorSpeedAngleDeriv G (p.1, (r, Θ (p.1, r))))) •
            circleVectorSpeedParameterDeriv G (p.1, (t, Θ (p.1, t)))

theorem contDiff_circleVectorTrajectoryParameterDerivative
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {n : ℕ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ n Θ) :
    ContDiff ℝ n (circleVectorTrajectoryParameterDerivative G Θ) := by
  have hK : ContDiff ℝ n (fun p : E × ℝ =>
      circleVectorSpeedAngleDeriv G (p.1, (p.2, Θ p))) :=
    (contDiff_infty.mp (contDiff_circleVectorSpeedAngleDeriv hG) n).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk hΘ))
  have hQ : ContDiff ℝ n (fun p : E × ℝ =>
      circleVectorSpeedParameterDeriv G (p.1, (p.2, Θ p))) :=
    (contDiff_infty.mp (contDiff_circleVectorSpeedParameterDeriv hG) n).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk hΘ))
  have hI := contDiff_parametric_primitive_nat hK (0 : ℝ)
  have hF : ContDiff ℝ n (fun p : E × ℝ =>
      Real.exp (-(∫ r in (0 : ℝ)..p.2,
        circleVectorSpeedAngleDeriv G (p.1, (r, Θ (p.1, r))))) •
          circleVectorSpeedParameterDeriv G (p.1, (p.2, Θ p))) :=
    (Real.contDiff_exp.comp hI.neg).smul hQ
  exact (Real.contDiff_exp.comp hI).smul (contDiff_parametric_primitive_nat hF 0)

theorem circleVectorTrajectoryParameterDerivative_apply
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ) (p : E × ℝ) (v : E) :
    circleVectorTrajectoryParameterDerivative G Θ p v =
      Real.exp (∫ r in (0 : ℝ)..p.2,
        circleVectorSpeedAngleDeriv G (p.1, (r, Θ (p.1, r)))) *
          ∫ t in (0 : ℝ)..p.2,
            Real.exp (-(∫ r in (0 : ℝ)..t,
              circleVectorSpeedAngleDeriv G (p.1, (r, Θ (p.1, r))))) *
                circleVectorSpeedParameterDeriv G (p.1, (t, Θ (p.1, t))) v := by
  have hK : Continuous (fun t : ℝ =>
      circleVectorSpeedAngleDeriv G (p.1, (t, Θ (p.1, t)))) :=
    (contDiff_circleVectorSpeedAngleDeriv hG).continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk
        (hΘ.comp (continuous_const.prodMk continuous_id))))
  have hQ : Continuous (fun t : ℝ =>
      circleVectorSpeedParameterDeriv G (p.1, (t, Θ (p.1, t)))) :=
    (contDiff_circleVectorSpeedParameterDeriv hG).continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk
        (hΘ.comp (continuous_const.prodMk continuous_id))))
  have hI : Continuous (fun t : ℝ => ∫ r in (0 : ℝ)..t,
      circleVectorSpeedAngleDeriv G (p.1, (r, Θ (p.1, r)))) :=
    continuous_iff_continuousAt.mpr
      (fun t => (hK.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt)
  have hF : Continuous (fun t : ℝ =>
      Real.exp (-(∫ r in (0 : ℝ)..t,
        circleVectorSpeedAngleDeriv G (p.1, (r, Θ (p.1, r))))) •
          circleVectorSpeedParameterDeriv G (p.1, (t, Θ (p.1, t)))) :=
    (Real.continuous_exp.comp hI.neg).smul hQ
  dsimp only [circleVectorTrajectoryParameterDerivative]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.intervalIntegral_apply (hF.intervalIntegrable 0 p.2) v]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The scalar-parameter theorem proves every actual vector-line
derivative.  The derivative values are evaluations of one CLM. -/
theorem globalCircleVectorTrajectory_hasDerivAt_line
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q : E, Θ (q, 0) = θ₀)
    (hflow : ∀ q : E, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    (q v : E) (s t : ℝ) :
    HasDerivAt (fun r : ℝ => Θ (q + r • v, t))
      (circleVectorTrajectoryParameterDerivative G Θ (q + s • v, t) v) s := by
  let Φ : PolarPoint → ℝ := fun p => Θ (q + p.1 • v, p.2)
  have hΦ : Continuous Φ :=
    hΘ.comp ((continuous_const.add (continuous_fst.smul continuous_const)).prodMk continuous_snd)
  have hd := globalCircleParameterTrajectory_hasDerivAt_parameter
    (contDiff_circleVectorSpeedLine hG q v) hΦ
    (fun r => hinit (q + r • v)) (fun r u => hflow (q + r • v) u) s t
  apply hd.congr_deriv
  rw [circleVectorTrajectoryParameterDerivative_apply hG hΘ]
  simp only [circleParameterTrajectoryDerivative, Φ,
    circleVectorSpeedLine_angleDeriv hG, circleVectorSpeedLine_parameterDeriv hG]

/-- The actual finite-dimensional parameter derivative of the supplied
trajectory, proved without differentiability hypotheses on that family. -/
theorem globalCircleVectorTrajectory_hasFDerivAt_parameter
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q : E, Θ (q, 0) = θ₀)
    (hflow : ∀ q : E, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    (q : E) (t : ℝ) :
    HasFDerivAt (fun y : E => Θ (y, t))
      (circleVectorTrajectoryParameterDerivative G Θ (q, t)) q :=
  hasFDerivAt_of_continuous_affine_line_derivatives
    ((contDiff_circleVectorTrajectoryParameterDerivative hG
      (contDiff_zero.mpr hΘ)).continuous.comp (continuous_id.prodMk continuous_const))
    (fun y v s => globalCircleVectorTrajectory_hasDerivAt_line hG hΘ hinit hflow y v s t) q

/-- All genuine joint Fréchet derivatives in finite-dimensional parameter
and time are obtained by induction from the variational formula. -/
theorem contDiff_globalCircleVectorTrajectory
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q : E, Θ (q, 0) = θ₀)
    (hflow : ∀ q : E, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t) :
    ContDiff ℝ ∞ Θ := by
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hΘ
  | succ n ih =>
    have hA : ContDiff ℝ n (circleVectorTrajectoryParameterDerivative G Θ) :=
      contDiff_circleVectorTrajectoryParameterDerivative hG ih
    let B : E × ℝ → ℝ := fun p => G (p.1, (p.2, Θ p))
    have hB : ContDiff ℝ n B :=
      (contDiff_infty.mp hG n).comp (contDiff_fst.prodMk (contDiff_snd.prodMk ih))
    have hBc : ContDiff ℝ n
        (fun p => ContinuousLinearMap.toSpanSingleton ℝ (B p)) := by
      apply contDiff_clm_apply_iff.mpr
      intro r
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
        (contDiff_const.mul hB : ContDiff ℝ n (fun p => r * B p))
    let D : E × ℝ → (E × ℝ) →L[ℝ] ℝ := fun p =>
      (circleVectorTrajectoryParameterDerivative G Θ p).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (B p))
    have hD : ContDiff ℝ n D := by
      apply contDiff_clm_apply_iff.mpr
      intro v
      simpa only [D, ContinuousLinearMap.coprod_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
        ((hA.clm_apply contDiff_const).add (contDiff_const.mul hB) :
          ContDiff ℝ n (fun p =>
            circleVectorTrajectoryParameterDerivative G Θ p v.1 + v.2 * B p))
    refine contDiff_succ_iff_hasFDerivAt.mpr ⟨D, hD, fun p => ?_⟩
    exact (hasStrictFDerivAt_uncurry_coprod
      (f := fun q t => Θ (q, t))
      (f₁ := fun q t => circleVectorTrajectoryParameterDerivative G Θ (q, t))
      (f₂ := fun q t => ContinuousLinearMap.toSpanSingleton ℝ (B (q, t)))
      (Eventually.of_forall (fun z =>
        globalCircleVectorTrajectory_hasFDerivAt_parameter hG hΘ hinit hflow z.1 z.2))
      (Eventually.of_forall (fun z => (hflow z.1 z.2).hasFDerivAt))
      hA.continuous.continuousAt hBc.continuous.continuousAt).hasFDerivAt

/-- A flat time change of the supplied, jointly continuous compact
family is smooth in every finite-dimensional speed parameter and new time. -/
theorem contDiff_circleVectorTrajectory_timeChange
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {a b θ₀ : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hΘ : ContinuousOn Θ ((univ : Set E) ×ˢ Icc a b))
    (hinit : ∀ q : E, Θ (q, a) = θ₀)
    (hflow : ∀ q : E, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (hτzero : τ 0 = a)
    (hτrange : ∀ s : ℝ, τ s ∈ Icc a b) :
    ContDiff ℝ ∞ (fun p : E × ℝ => Θ (p.1, τ p.2)) := by
  let V : E × PolarPoint → ℝ := fun p =>
    deriv τ p.2.1 * G (p.1, (τ p.2.1, p.2.2))
  have hV : ContDiff ℝ ∞ V :=
    ((contDiff_infty_iff_deriv.mp hτ).2.comp contDiff_snd.fst).mul
      (hG.comp (contDiff_fst.prodMk
        ((hτ.comp contDiff_snd.fst).prodMk contDiff_snd.snd)))
  have hcontinuous : Continuous (fun p : E × ℝ => Θ (p.1, τ p.2)) :=
    hΘ.comp_continuous (continuous_fst.prodMk (hτ.continuous.comp continuous_snd))
      (fun p => ⟨mem_univ p.1, hτrange p.2⟩)
  have htime (q : E) : ContinuousOn (fun r => Θ (q, r)) (Icc a b) :=
    hΘ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun r hr => ⟨mem_univ q, hr⟩)
  have hinitial (q : E) : Θ (q, τ 0) = θ₀ := by rw [hτzero, hinit q]
  have htime' (q : E) (s : ℝ) : HasDerivAt (fun r => Θ (q, τ r))
      (V (q, (s, Θ (q, τ s)))) s :=
    hasDerivAt_timeChange_classicalTrajectory ((hτrange 0).1.trans (hτrange 0).2)
      (hG.continuous.comp (continuous_const.prodMk continuous_id))
      (htime q) (fun r hr => hflow q r hr) hτrange
      ((hτ.differentiable (by simp) s).hasDerivAt)
  exact contDiff_globalCircleVectorTrajectory hV hcontinuous hinitial htime'

/-- Every actual compact-interval time slice, including an endpoint,
has all finite-dimensional parameter derivatives. -/
theorem circleVectorTrajectory_contDiff_parameter
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {a b θ₀ : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hΘ : ContinuousOn Θ ((univ : Set E) ×ˢ Icc a b))
    (hinit : ∀ q : E, Θ (q, a) = θ₀)
    (hflow : ∀ q : E, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun q => Θ (q, t)) := by
  have hsmooth := contDiff_circleVectorTrajectory_timeChange hG hΘ hinit hflow
    (contDiff_circleFlowCompactTime a b) (circleFlowCompactTime_zero a b)
    (circleFlowCompactTime_mem (ht.1.trans ht.2))
  obtain ⟨s, _, hs⟩ := circleFlowCompactTime_surjOn a b ht
  have hslice : ContDiff ℝ ∞ (fun q => Θ (q, circleFlowCompactTime a b s)) :=
    hsmooth.comp (contDiff_id.prodMk contDiff_const)
  simpa only [hs] using hslice

end ContinuousFlexibility.Analysis
