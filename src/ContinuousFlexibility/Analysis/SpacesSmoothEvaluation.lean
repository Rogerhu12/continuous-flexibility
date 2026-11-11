import ContinuousFlexibility.Analysis.ProjectiveDifferential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Smooth evaluation along curves in a Fréchet space

For a barrelled real vector space, pointwise continuous linear evaluation
of smooth functions has continuous derivative evaluations. The first
assertion follows from Banach--Steinhaus on a compact neighbourhood. The
second follows by applying Banach--Steinhaus to ordinary difference
quotients. Together they justify joint smoothness along actual smooth
curves, including at a boundary already crossed by the individual smooth
functions. No uniform weighted estimate is assumed in this argument.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

section EvaluationContinuity

variable {E : Type*} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
  [IsUniformAddGroup E] [ContinuousSMul ℝ E] [BarrelledSpace ℝ E]
variable {P : Type*} [NormedAddCommGroup P] [ProperSpace P]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise continuous linear evaluation is jointly continuous when the
parameter space is locally compact and the source is barrelled. -/
theorem spaces_continuous_evaluation (L : P → E →L[ℝ] F)
    (hL : ∀ u : E, Continuous (fun p => L p u)) :
    Continuous (fun z : P × E => L z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨p₀, u₀⟩
  let K : Set P := Metric.closedBall p₀ 1
  have hK : IsCompact K := isCompact_closedBall p₀ 1
  have hbounded : ∀ (_ : Unit) (u : E),
      BddAbove (range fun p : K => (normSeminorm ℝ F) (L p.val u)) := by
    intro _ u
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hL u).continuousOn
    refine ⟨C, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact hC p.val p.property
  have heq : Equicontinuous (fun p : K => (L p.val : E → F)) :=
    ((norm_withSeminorms ℝ F).banach_steinhaus hbounded).equicontinuous
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε₂ : 0 < ε / 2 := half_pos hε
  have hu := Metric.equicontinuousAt_iff_right.mp (heq u₀) (ε / 2) hε₂
  have hp := Metric.tendsto_nhds.mp ((hL u₀).continuousAt (x := p₀)) (ε / 2) hε₂
  have hnear : K ∈ 𝓝 p₀ := Metric.closedBall_mem_nhds p₀ zero_lt_one
  filter_upwards [continuous_snd.continuousAt.eventually hu,
    continuous_fst.continuousAt.eventually hp,
    continuous_fst.continuousAt.eventually hnear] with z hzu hzp hzK
  calc
    dist (L z.1 z.2) (L p₀ u₀) ≤
        dist (L z.1 z.2) (L z.1 u₀) + dist (L z.1 u₀) (L p₀ u₀) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by
      simpa only [dist_comm] using hzu ⟨z.1, hzK⟩) hzp
    _ = ε := add_halves ε

end EvaluationContinuity

section DifferentialEvaluation

variable {E : Type*} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
  [IsUniformAddGroup E] [ContinuousSMul ℝ E] [BarrelledSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Each coordinate derivative of a smooth family of continuous linear
maps is again a continuous linear map in the vector-space argument. -/
def spaces_coordinateDerivative (L : (ℝ × ℝ) → E →L[ℝ] F)
    (hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u)) (p v : ℝ × ℝ) : E →L[ℝ] F := by
  let A : E →L[ℝ] F := continuousLinearMapOfTendsto
    (l := 𝓝[≠] (0 : ℝ)) (fun t => t⁻¹ • (L (p + t • v) - L p))
    (f := fun u => (fderiv ℝ (fun q => L q u) p) v) (by
      apply tendsto_pi_nhds.mpr
      intro u
      have hdu := ((hL u).differentiable (by simp) (p + (0 : ℝ) • v)).hasFDerivAt
      have hv : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
        simpa only [id_eq, one_smul] using
          ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
      have hd := hdu.comp_hasDerivAt 0 hv
      simpa only [Function.comp_apply, zero_smul, add_zero, zero_add, smul_apply,
        sub_apply] using hasDerivAt_iff_tendsto_slope_zero.mp hd)
  exact { toFun := fun u => (fderiv ℝ (fun q => L q u) p) v
          map_add' := A.map_add
          map_smul' := A.map_smul
          cont := A.continuous }

@[simp] theorem spaces_coordinateDerivative_apply
    (L : (ℝ × ℝ) → E →L[ℝ] F)
    (hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u)) (p v : ℝ × ℝ) (u : E) :
    spaces_coordinateDerivative L hL p v u = (fderiv ℝ (fun q => L q u) p) v := rfl

/-- Full spatial derivative evaluation on the polar coordinate plane. -/
def spaces_differentialEvaluation (L : (ℝ × ℝ) → E →L[ℝ] F)
    (hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u)) (p : ℝ × ℝ) :
    E →L[ℝ] ((ℝ × ℝ) →L[ℝ] F) :=
  (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp (spaces_coordinateDerivative L hL p (1, 0)) +
  (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F
      (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp (spaces_coordinateDerivative L hL p (0, 1))

@[simp] theorem spaces_differentialEvaluation_apply
    (L : (ℝ × ℝ) → E →L[ℝ] F)
    (hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u)) (p : ℝ × ℝ) (u : E) :
    spaces_differentialEvaluation L hL p u = fderiv ℝ (fun q => L q u) p := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨r, θ⟩
  simp only [spaces_differentialEvaluation, add_apply,
    ContinuousLinearMap.comp_apply, spaces_coordinateDerivative_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have he : (r, θ) = r • ((1, 0) : ℝ × ℝ) + θ • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [he, map_add, map_smul, map_smul]

/-- Spatial differentiation preserves pointwise smoothness. -/
theorem spaces_differentialEvaluation_contDiff
    (L : (ℝ × ℝ) → E →L[ℝ] F)
    (hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u)) (u : E) :
    ContDiff ℝ ∞ (fun p => spaces_differentialEvaluation L hL p u) := by
  simpa only [spaces_differentialEvaluation_apply] using
    (hL u).fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)

private theorem spaces_hasFDerivAt_evaluation_curve_aux
    (L : (ℝ × ℝ) → E →L[ℝ] F)
    (DL : (ℝ × ℝ) → E →L[ℝ] ((ℝ × ℝ) →L[ℝ] F))
    (hL : ∀ u : E, Continuous (fun p => L p u))
    (hDL : ∀ u : E, Continuous (fun p => DL p u))
    (hspatial : ∀ (u : E) (p : ℝ × ℝ), HasFDerivAt (fun q => L q u) (DL p u) p)
    {U : Set ℝ} (hU : IsOpen U) {c dc : ℝ → E}
    (hc : ContinuousOn c U) (hdc : ContinuousOn dc U)
    (hderiv : ∀ t ∈ U, HasProjectiveCurveDerivAt c (dc t) t)
    {z : (ℝ × ℝ) × ℝ} (hz : z ∈ univ ×ˢ U) :
    HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => L y.1 (c y.2))
      ((DL z.1 (c z.2)).comp
          (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) +
        (ContinuousLinearMap.toSpanSingleton ℝ (L z.1 (dc z.2))).comp
          (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)) z := by
  have hV : IsOpen ((univ : Set (ℝ × ℝ)) ×ˢ U) := isOpen_univ.prod hU
  have hDcont : ContinuousOn
      (fun y : (ℝ × ℝ) × ℝ => DL y.1 (c y.2)) (univ ×ˢ U) :=
    (spaces_continuous_evaluation DL hDL).comp_continuousOn
        (continuousOn_fst.prodMk (hc.comp continuousOn_snd (fun _ hy => hy.2)))
  have hdcEval : ContinuousOn
      (fun y : (ℝ × ℝ) × ℝ => L y.1 (dc y.2)) (univ ×ˢ U) :=
    (spaces_continuous_evaluation L hL).comp_continuousOn
      (continuousOn_fst.prodMk (hdc.comp continuousOn_snd (fun _ hy => hy.2)))
  have hsecond : ContinuousOn
      (fun y : (ℝ × ℝ) × ℝ => ContinuousLinearMap.toSpanSingleton ℝ (L y.1 (dc y.2)))
      (univ ×ˢ U) := by
    simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingletonLIE_apply] using
      (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp_continuousOn hdcEval
  have hx : ∀ᶠ y : (ℝ × ℝ) × ℝ in 𝓝 z,
      HasFDerivAt (fun p => L p (c y.2)) (DL y.1 (c y.2)) y.1 := by
    exact Eventually.of_forall (fun y => hspatial (c y.2) y.1)
  have ht : ∀ᶠ y : (ℝ × ℝ) × ℝ in 𝓝 z,
      HasFDerivAt (fun t => L y.1 (c t))
        (ContinuousLinearMap.toSpanSingleton ℝ (L y.1 (dc y.2))) y.2 := by
    filter_upwards [hV.mem_nhds hz] with y hy
    have hcurve : HasDerivAt (fun t : ℝ => L y.1 (c t)) (L y.1 (dc y.2)) y.2 :=
      hasDerivAt_iff_tendsto_slope_zero.mpr ((hderiv y.2 hy.2).clm_comp (L y.1))
    exact hcurve.hasFDerivAt
  have hd := hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℝ) (u := z)
    (f := fun p t => L p (c t))
    (f₁ := fun p t => DL p (c t))
    (f₂ := fun p t => ContinuousLinearMap.toSpanSingleton ℝ (L p (dc t)))
    hx ht (hDcont.continuousAt (hV.mem_nhds hz))
      (hsecond.continuousAt (hV.mem_nhds hz))
  rw [ContinuousLinearMap.comp_fst_add_comp_snd]
  exact hd.hasFDerivAt

/-- The first derivative of evaluation along an actual topological curve.
The two partial derivatives are continuous by Banach--Steinhaus, so the
usual theorem on continuous partial derivatives applies. -/
theorem spaces_hasFDerivAt_evaluation_curve
    (L : (ℝ × ℝ) → E →L[ℝ] F)
    (hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u))
    {U : Set ℝ} (hU : IsOpen U) {c dc : ℝ → E}
    (hc : ContinuousOn c U) (hdc : ContinuousOn dc U)
    (hderiv : ∀ t ∈ U, HasProjectiveCurveDerivAt c (dc t) t)
    {z : (ℝ × ℝ) × ℝ} (hz : z ∈ univ ×ˢ U) :
    HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => L y.1 (c y.2))
      ((spaces_differentialEvaluation L hL z.1 (c z.2)).comp
          (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) +
        (ContinuousLinearMap.toSpanSingleton ℝ (L z.1 (dc z.2))).comp
          (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)) z := by
  apply spaces_hasFDerivAt_evaluation_curve_aux L (spaces_differentialEvaluation L hL)
    (fun u => (hL u).continuous)
    (fun u => (spaces_differentialEvaluation_contDiff L hL u).continuous)
    (fun u p => ?_) hU hc hdc hderiv hz
  rw [spaces_differentialEvaluation_apply]
  exact ((hL u).differentiable (by simp) p).hasFDerivAt

/-- Every finite smoothness order of joint evaluation follows from an
actual continuous derivative tower for the curve. -/
theorem spaces_contDiffOn_nat_evaluation_curve (n : ℕ)
    (L : (ℝ × ℝ) → E →L[ℝ] F)
    (hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u))
    {U : Set ℝ} (hU : IsOpen U) (c : ℕ → ℝ → E)
    (hc : ∀ k, ContinuousOn (c k) U)
    (hderiv : ∀ k t, t ∈ U → HasProjectiveCurveDerivAt (c k) (c (k + 1) t) t) :
    ContDiffOn ℝ n (fun z : (ℝ × ℝ) × ℝ => L z.1 (c 0 z.2)) (univ ×ˢ U) := by
  induction n generalizing F c with
  | zero =>
    exact contDiffOn_zero.mpr
      ((spaces_continuous_evaluation L (fun u => (hL u).continuous)).comp_continuousOn
        (continuousOn_fst.prodMk ((hc 0).comp continuousOn_snd (fun _ hz => hz.2))))
  | succ n ih =>
    let DL := spaces_differentialEvaluation L hL
    have hDL : ∀ u : E, ContDiff ℝ ∞ (fun p => DL p u) :=
      spaces_differentialEvaluation_contDiff L hL
    have hfirst : ContDiffOn ℝ n
        (fun z : (ℝ × ℝ) × ℝ => (DL z.1 (c 0 z.2)).comp
          (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)) (univ ×ˢ U) :=
      (ih DL hDL c hc hderiv).clm_comp contDiffOn_const
    have htail : ContDiffOn ℝ n
        (fun z : (ℝ × ℝ) × ℝ => L z.1 (c 1 z.2)) (univ ×ˢ U) :=
      ih L hL (fun k => c (k + 1)) (fun k => hc (k + 1))
        (fun k t ht => hderiv (k + 1) t ht)
    have hsecond : ContDiffOn ℝ n
        (fun z : (ℝ × ℝ) × ℝ =>
          (ContinuousLinearMap.toSpanSingleton ℝ (L z.1 (c 1 z.2))).comp
            (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)) (univ ×ˢ U) := by
      have hspan := (ContinuousLinearMap.toSpanSingletonLIE ℝ F).contDiff.comp_contDiffOn htail
      simpa only [Function.comp_apply, ContinuousLinearMap.toSpanSingletonLIE_apply] using
        hspan.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ))
    have hV : IsOpen ((univ : Set (ℝ × ℝ)) ×ˢ U) := isOpen_univ.prod hU
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (hV.uniqueDiffOn (𝕜 := ℝ))).mpr
    refine ⟨by simp, _, hfirst.add hsecond, ?_⟩
    intro z hz
    exact (spaces_hasFDerivAt_evaluation_curve L hL hU (hc 0) (hc 1)
      (hderiv 0) hz).hasFDerivWithinAt

/-- Joint smoothness along a genuinely smooth curve, with no shrinking of
the parameter domain as the derivative order increases. -/
theorem spaces_contDiffOn_evaluation_curve
    (L : (ℝ × ℝ) → E →L[ℝ] F)
    (hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u))
    {U : Set ℝ} (hU : IsOpen U) (c : ℕ → ℝ → E)
    (hc : ∀ k, ContinuousOn (c k) U)
    (hderiv : ∀ k t, t ∈ U → HasProjectiveCurveDerivAt (c k) (c (k + 1) t) t) :
    ContDiffOn ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => L z.1 (c 0 z.2)) (univ ×ˢ U) :=
  contDiffOn_infty.mpr (fun n => spaces_contDiffOn_nat_evaluation_curve n L hL hU c hc hderiv)

end DifferentialEvaluation

end ContinuousFlexibility.Analysis
