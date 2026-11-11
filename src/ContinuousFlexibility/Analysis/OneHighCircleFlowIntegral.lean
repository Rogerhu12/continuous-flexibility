import ContinuousFlexibility.Scalar.RectangleParameterIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Smooth dependence of compact interval integrals on their parameters

Differentiation under a fixed compact integral is justified by a local
compact bound for the actual Fréchet derivative.  Induction gives every
finite order, and affine change of variables handles a moving endpoint.
The parameter spaces used for circle flows are `ℝ` and `ℝ × ℝ`; the
statements work in any finite-dimensional real normed parameter space.
The smooth fixed-interval statement reuses the compact-parameter API.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

variable {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A jointly continuous integrand has a continuous fixed-interval
integral, with either orientation of the endpoints. -/
theorem continuous_parametric_intervalIntegral {F : H × ℝ → E}
    (hF : Continuous F) (a b : ℝ) :
    Continuous (fun x : H => ∫ t in a..b, F (x, t)) := by
  have hc (c d : ℝ) : Continuous (fun x : H => ∫ t in Icc c d, F (x, t)) :=
    continuous_parametric_integral_of_continuous (f := fun x t => F (x, t))
      hF isCompact_Icc
  rcases le_total a b with hab | hba
  · simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
      using hc a b
  · have hn : Continuous (fun x : H => -(∫ t in Icc b a, F (x, t))) := by
      simpa only [Function.comp_def] using continuous_neg.comp (hc b a)
    simpa only [intervalIntegral.integral_of_ge hba, integral_Icc_eq_integral_Ioc]
      using hn

/-- Continuous actual parameter derivatives can be moved under a compact
interval integral. The local domination is obtained, rather than assumed. -/
theorem hasFDerivAt_parametric_intervalIntegral
    {F : H × ℝ → E} {F' : H × ℝ → H →L[ℝ] E}
    (hF : Continuous F) (hF' : Continuous F')
    (hderiv : ∀ x : H, ∀ t : ℝ,
      HasFDerivAt (fun y : H => F (y, t)) (F' (x, t)) x)
    (a b : ℝ) (x : H) :
    HasFDerivAt (fun y : H => ∫ t in a..b, F (y, t))
      (∫ t in a..b, F' (x, t)) x := by
  have hcompact : IsCompact (Metric.closedBall x 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall x 1).prod isCompact_uIcc
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hF'.continuousOn
  have hs : Metric.closedBall x 1 ∈ 𝓝 x := Metric.closedBall_mem_nhds x zero_lt_one
  have hsection (y : H) : Continuous (fun t : ℝ => F (y, t)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hsection' (y : H) : Continuous (fun t : ℝ => F' (y, t)) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => F (y, t)) (F' := fun y t => F' (y, t))
    (μ := volume) (a := a) (b := b) (s := Metric.closedBall x 1)
    (bound := fun _ : ℝ => B) hs
    (Eventually.of_forall (fun y => (hsection y).aestronglyMeasurable))
    ((hsection x).intervalIntegrable a b)
    ((hsection' x).aestronglyMeasurable)
    (Eventually.of_forall (fun t ht y hy => hB (y, t) ⟨hy, uIoc_subset_uIcc ht⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun t _ y _ => hderiv y t))

/-- Fixed compact integration preserves every finite differentiability
order, including genuine joint parameter differentiability. -/
theorem contDiff_parametric_intervalIntegral_nat {n : ℕ} {F : H × ℝ → E}
    (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun x : H => ∫ t in a..b, F (x, t)) := by
  induction n generalizing E with
  | zero =>
    exact contDiff_zero.mpr (continuous_parametric_intervalIntegral hF.continuous a b)
  | succ n ih =>
    let D : H × ℝ → H →L[ℝ] E := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ H ℝ)
    have hD : ContDiff ℝ n D :=
      (hF.fderiv_right (m := (n : ℕ∞ω)) (by simp)).clm_comp contDiff_const
    have hd (x : H) (t : ℝ) : HasFDerivAt (fun y : H => F (y, t)) (D (x, t)) x :=
      ((hF.differentiable (by simp) (x, t)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left x t))
    have hI : ContDiff ℝ n (fun x : H => ∫ t in a..b, D (x, t)) := ih hD
    exact contDiff_succ_iff_hasFDerivAt.mpr
      ⟨_, hI, fun x => hasFDerivAt_parametric_intervalIntegral
        hF.continuous hD.continuous hd a b x⟩

theorem contDiff_parametric_intervalIntegral {F : H × ℝ → E}
    (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x : H => ∫ t in a..b, F (x, t)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  rcases le_total a b with hab | hba
  · exact contDiffAt_intervalIntegral_parameter (O := univ) isOpen_univ hab
      (fun _ _ _ _ => hF.contDiffAt) (mem_univ x)
  · have hc : ContDiffAt ℝ ∞ (fun y : H => ∫ t in b..a, F (y, t)) x :=
      contDiffAt_intervalIntegral_parameter (O := univ) isOpen_univ hba
        (fun _ _ _ _ => hF.contDiffAt) (mem_univ x)
    simpa only [intervalIntegral.integral_symm a b, neg_neg] using hc.neg

/-- The endpoint and all other parameters may vary together. Affine
rescaling also includes the zero-length interval without a division. -/
theorem contDiff_parametric_primitive_nat {n : ℕ} {F : H × ℝ → E}
    (hF : ContDiff ℝ n F) (a : ℝ) :
    ContDiff ℝ n (fun p : H × ℝ => ∫ t in a..p.2, F (p.1, t)) := by
  have hscaled : ContDiff ℝ n (fun q : (H × ℝ) × ℝ =>
      F (q.1.1, (q.1.2 - a) * q.2 + a)) :=
    hF.comp (contDiff_fst.fst.prodMk
      (((contDiff_fst.snd.sub contDiff_const).mul contDiff_snd).add contDiff_const))
  have hI := contDiff_parametric_intervalIntegral_nat hscaled (0 : ℝ) 1
  have hproduct : ContDiff ℝ n (fun p : H × ℝ =>
      (p.2 - a) • ∫ t in (0 : ℝ)..1, F (p.1, (p.2 - a) * t + a)) :=
    (contDiff_snd.sub contDiff_const).smul hI
  have he : (fun p : H × ℝ => ∫ t in a..p.2, F (p.1, t)) =
      fun p : H × ℝ => (p.2 - a) •
        ∫ t in (0 : ℝ)..1, F (p.1, (p.2 - a) * t + a) := by
    funext p
    simpa only [mul_zero, zero_add, mul_one, sub_add_cancel] using
      (intervalIntegral.smul_integral_comp_mul_add (fun t => F (p.1, t))
        (a := (0 : ℝ)) (b := 1) (p.2 - a) a).symm
  rw [he]
  exact hproduct

theorem contDiff_parametric_primitive {F : H × ℝ → E}
    (hF : ContDiff ℝ ∞ F) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : H × ℝ => ∫ t in a..p.2, F (p.1, t)) :=
  contDiff_infty.mpr (fun n =>
    contDiff_parametric_primitive_nat (contDiff_infty.mp hF n) a)

end ContinuousFlexibility.Analysis
