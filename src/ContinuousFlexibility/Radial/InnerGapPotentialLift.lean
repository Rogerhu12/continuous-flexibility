import ContinuousFlexibility.Radial.InnerGapRadialDomain
import ContinuousFlexibility.Radial.InnerWeightL2
import ContinuousFlexibility.Radial.InnerRadialL2Pairing

/-!
# The positive-gap form on the common physical H¹ domain

The potential square-root coefficient is bounded on the retained
compact positive interval. Its actual multiplication operator supplies
a continuous inverse to the projection from the three-coordinate
coercive domain to the common function/derivative domain.

Consequently the constructed gap inverse satisfies the form equation
against every test in that common H¹ domain, not just projected tests.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

def innerGapPotentialWeight (D : ReferenceData) (j a b : ℝ) : ℝ → ℝ :=
  (Ioo a b).indicator (fun r => Real.sqrt ((j ^ 2 / 12) * (r * deriv D.w r / D.w r)))

theorem innerGapPotentialWeight_measurable (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    (j a b : ℝ) : Measurable (innerGapPotentialWeight D j a b) :=
  (Real.continuous_sqrt.measurable.comp
    (measurable_const.mul
      ((measurable_id.mul (contDiff_infty_iff_deriv.mp hw).2.continuous.measurable).div
        hw.continuous.measurable))).indicator measurableSet_Ioo

theorem innerGapPotentialWeight_bounded (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, |innerGapPotentialWeight D j a b r| ≤ C := by
  have hc : ContinuousOn
      (fun r => Real.sqrt ((j ^ 2 / 12) * (r * deriv D.w r / D.w r))) (Icc a b) := by
    simpa only [innerGapPotentialField, mul_one] using
      (innerGapPotentialField_continuousOn (u := fun _ : ℝ => (1 : ℝ))
        hw contDiff_const hpos j)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r
  by_cases hr : r ∈ Ioo a b
  · rw [innerGapPotentialWeight, indicator_of_mem hr]
    have hb : |Real.sqrt ((j ^ 2 / 12) * (r * deriv D.w r / D.w r))| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC r (Ioo_subset_Icc_self hr)
    exact hb.trans (le_max_left _ _)
  · rw [innerGapPotentialWeight, indicator_of_notMem hr, abs_zero]
    exact le_max_right _ _

/-- The actual bounded potential square-root multiplier in μ_D. -/
def innerGapPotentialMultiplier (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) :
    RadialModeL2 D →L[ℝ] RadialModeL2 D :=
  let hB := innerGapPotentialWeight_bounded D hw hpos j
  innerWeightMultiplier (radialHilbertMeasure D) (innerGapPotentialWeight D j a b)
    (innerGapPotentialWeight_measurable D hw j a b) hB.choose hB.choose_spec.2

theorem innerGapPotentialMultiplier_ae (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) (u : RadialModeL2 D) :
    innerGapPotentialMultiplier D hw hpos j u =ᵐ[radialHilbertMeasure D]
      fun r => innerGapPotentialWeight D j a b r * u r := by
  dsimp only [innerGapPotentialMultiplier]
  exact innerWeightMultiplier_ae _ _ _ _ _ u

/-- Adjoin the actual potential coordinate to a physical H¹ pair. -/
def innerGapPotentialLift (D : ReferenceData) (M : RadialModeL2 D →L[ℝ] RadialModeL2 D) :
    InnerRadialH1Pair D →L[ℝ] InnerGapEnergyTriple D :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).symm :
    (RadialModeL2 D × InnerGapEnergyPair D) →L[ℝ] InnerGapEnergyTriple D) ∘L
      (ContinuousLinearMap.fst ℝ (RadialModeL2 D) (RadialModeL2 D)).prod
        (((WithLp.prodContinuousLinearEquiv 2 ℝ (RadialModeL2 D) (RadialModeL2 D)).symm :
          InnerRadialH1Pair D →L[ℝ] InnerGapEnergyPair D) ∘L
            (ContinuousLinearMap.snd ℝ (RadialModeL2 D) (RadialModeL2 D)).prod
              (M ∘L ContinuousLinearMap.fst ℝ (RadialModeL2 D) (RadialModeL2 D)))

theorem innerGapPotentialLift_apply (D : ReferenceData)
    (M : RadialModeL2 D →L[ℝ] RadialModeL2 D) (v : InnerRadialH1Pair D) :
    innerGapPotentialLift D M v = WithLp.toLp 2 (v.1, WithLp.toLp 2 (v.2, M v.1)) := by
  simp only [innerGapPotentialLift, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply]

theorem innerGapPotentialLift_core (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (v : InnerRadialH1Pair D) (hv : v ∈ InnerRadialH1Core D a b) :
    innerGapPotentialLift D (innerGapPotentialMultiplier D hw hpos j) v ∈
      InnerGapEnergyCore D j a b := by
  rcases hv with ⟨u, hu, hcompact, hsupport, hvalue, hgrad⟩
  rw [innerGapPotentialLift_apply]
  refine ⟨u, hu, hcompact, hsupport, ?_, ?_, ?_⟩
  · simpa only [WithLp.toLp_fst] using hvalue
  · simpa only [WithLp.toLp_snd, WithLp.toLp_fst] using hgrad
  · simp only [WithLp.toLp_snd]
    filter_upwards [innerGapPotentialMultiplier_ae D hw hpos j v.1, hvalue] with r hM hr
    rw [hM, hr]
    by_cases hmem : r ∈ Ioo a b
    · simp only [innerGapPotentialWeight, indicator_of_mem hmem, innerGapPotentialField]
    · simp only [innerGapPotentialWeight, indicator_of_notMem hmem, mul_zero]

/-- Every common physical H¹ test has its actual potential coordinate
in the coercive three-coordinate domain. -/
theorem innerGapPotentialLift_mem (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (v : InnerRadialH1Pair D) (hv : v ∈ innerRadialH1Zero D a b) :
    innerGapPotentialLift D (innerGapPotentialMultiplier D hw hpos j) v ∈
      innerGapFormSpace D j a b := by
  have hclosed : IsClosed {v : InnerRadialH1Pair D |
      innerGapPotentialLift D (innerGapPotentialMultiplier D hw hpos j) v ∈
        innerGapFormSpace D j a b} :=
    (innerGapFormSpace D j a b).isClosed.preimage
      (innerGapPotentialLift D (innerGapPotentialMultiplier D hw hpos j)).continuous
  apply (closure_minimal ?_ hclosed) ((mem_innerRadialH1Zero D a b v).mp hv)
  intro z hz
  exact (mem_innerGapFormSpace D j a b _).mpr
    (subset_closure (innerGapPotentialLift_core D hw hpos j z hz))

theorem innerGapFormSpace_potential (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) :
    q.snd.snd = innerGapPotentialMultiplier D hw hpos j q.fst := by
  let M := innerGapPotentialMultiplier D hw hpos j
  have hf : Continuous (fun q : InnerGapEnergyTriple D => M q.fst) :=
    M.continuous.comp (WithLp.fstL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hp : Continuous (fun q : InnerGapEnergyTriple D => q.snd.snd) :=
    (WithLp.sndL 2 ℝ (RadialModeL2 D) (RadialModeL2 D)).continuous.comp
      (WithLp.sndL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hclosed : IsClosed {q : InnerGapEnergyTriple D | q.snd.snd = M q.fst} :=
    isClosed_eq hp hf
  apply (closure_minimal ?_ hclosed) ((mem_innerGapFormSpace D j a b q).mp hq)
  rintro v ⟨u, _, _, _, hvalue, _, hpot⟩
  apply Lp.ext
  filter_upwards [hpot, innerGapPotentialMultiplier_ae D hw hpos j v.fst, hvalue]
    with r hp hM hv
  rw [hp, hM, hv]
  by_cases hmem : r ∈ Ioo a b
  · simp only [innerGapPotentialWeight, indicator_of_mem hmem, innerGapPotentialField]
  · simp only [innerGapPotentialWeight, indicator_of_notMem hmem, mul_zero]

/-- Exact form-graph identification with the common physical H¹ domain.
The same derivative works for every test; the potential multiplier is
constructed from the actual coefficient. -/
theorem innerGapFormGraph_iff_radialH1 (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) (u f : RadialModeL2 D) :
    InnerGapFormGraph D j a b u f ↔
      ∃ d : RadialModeL2 D, (u, d) ∈ innerRadialH1Zero D a b ∧
        ∀ v ∈ innerRadialH1Zero D a b,
          ⟪f, v.1⟫_ℝ = ⟪d, v.2⟫_ℝ +
            ⟪innerGapPotentialMultiplier D hw hpos j u,
              innerGapPotentialMultiplier D hw hpos j v.1⟫_ℝ := by
  let M := innerGapPotentialMultiplier D hw hpos j
  constructor
  · intro h
    obtain ⟨q, hq, hvalue, hform⟩ := (innerGapFormGraph_iff D j a b u f).mp h
    refine ⟨q.snd.fst, ?_, ?_⟩
    · simpa only [hvalue] using innerGapFormSpace_radialH1 D j a b q hq
    · intro v hv
      have ht := innerGapPotentialLift_mem D hw hpos j v hv
      have he := hform (innerGapPotentialLift D M v) ht
      have hp := innerGapFormSpace_potential D hw hpos j q hq
      simpa only [innerGapPotentialLift_apply, WithLp.toLp_fst, WithLp.toLp_snd,
        WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, hp, hvalue] using he
  · rintro ⟨d, hd, hform⟩
    apply (innerGapFormGraph_iff D j a b u f).mpr
    refine ⟨innerGapPotentialLift D M (u, d),
      innerGapPotentialLift_mem D hw hpos j (u, d) hd, ?_, ?_⟩
    · simp only [innerGapPotentialLift_apply, WithLp.toLp_fst]
    · intro r hr
      have he := hform (r.fst, r.snd.fst) (innerGapFormSpace_radialH1 D j a b r hr)
      have hp := innerGapFormSpace_potential D hw hpos j r hr
      simpa only [innerGapPotentialLift_apply, WithLp.toLp_snd, WithLp.prod_inner_apply,
        WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.toLp_fst, hp] using he

/-- The potential pairing is the actual physical radial potential
integral, for arbitrary L² fields. -/
theorem innerGapPotentialMultiplier_inner (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r) (j : ℝ)
    (u v : RadialModeL2 D) :
    ⟪innerGapPotentialMultiplier D hw hpos j u,
      innerGapPotentialMultiplier D hw hpos j v⟫_ℝ =
      ∫ r in Ioo a b, (j ^ 2 * deriv D.w r / r) * u r * v r := by
  rw [L2.inner_def]
  calc
    _ = ∫ r, (Ioo a b).indicator
        (fun r => ((j ^ 2 / 12) * (r * deriv D.w r / D.w r)) * u r * v r) r
          ∂radialHilbertMeasure D := by
      apply integral_congr_ae
      filter_upwards [innerGapPotentialMultiplier_ae D hw hpos j u,
        innerGapPotentialMultiplier_ae D hw hpos j v] with r hu hv
      rw [hu, hv]
      by_cases hr : r ∈ Ioo a b
      · have hα : 0 ≤ (j ^ 2 / 12) * (r * deriv D.w r / D.w r) :=
          mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
            (hslope r (Ioo_subset_Icc_self hr))
        simp only [innerGapPotentialWeight, indicator_of_mem hr, RCLike.inner_apply, conj_trivial]
        calc
          _ = Real.sqrt ((j ^ 2 / 12) * (r * deriv D.w r / D.w r)) ^ 2 * u r * v r := by ring
          _ = _ := by rw [Real.sq_sqrt hα]
      · simp only [innerGapPotentialWeight, indicator_of_notMem hr, zero_mul, inner_zero_left]
    _ = ∫ r in Ioo a b, ((j ^ 2 / 12) * (r * deriv D.w r / D.w r)) * u r * v r
        ∂radialHilbertMeasure D := integral_indicator measurableSet_Ioo
    _ = _ := by
      rw [innerRadialInterval_integral D hw.continuous hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      field_simp [(ha.trans hr.1).ne', (hpos r (Ioo_subset_Icc_self hr)).ne'] <;> ring


/-- The multiplier is self-adjoint on the actual real Hilbert space. -/
theorem innerGapPotentialMultiplier_adjoint (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) :
    (innerGapPotentialMultiplier D hw hpos j).adjoint =
      innerGapPotentialMultiplier D hw hpos j := by
  dsimp only [innerGapPotentialMultiplier]
  exact innerWeightMultiplier_adjoint _ _ _ _ _

/-- Squaring the constructed square-root multiplier gives the actual
signed radial potential on a positive piece. -/
theorem innerGapPotentialMultiplier_square_ae (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (u : RadialModeL2 D) :
    innerGapPotentialMultiplier D hw hpos j
        (innerGapPotentialMultiplier D hw hpos j u) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator
        (fun r => ((j ^ 2 / 12) * (r * deriv D.w r / D.w r)) * u r) := by
  filter_upwards [innerGapPotentialMultiplier_ae D hw hpos j
    (innerGapPotentialMultiplier D hw hpos j u),
    innerGapPotentialMultiplier_ae D hw hpos j u] with r houter hinner
  rw [houter, hinner]
  by_cases hr : r ∈ Ioo a b
  · have hα : 0 ≤ (j ^ 2 / 12) * (r * deriv D.w r / D.w r) :=
      mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
        (hslope r (Ioo_subset_Icc_self hr))
    simp only [innerGapPotentialWeight, indicator_of_mem hr]
    calc
      _ = Real.sqrt ((j ^ 2 / 12) * (r * deriv D.w r / D.w r)) ^ 2 * u r := by ring
      _ = _ := by rw [Real.sq_sqrt hα]
  · simp only [innerGapPotentialWeight, indicator_of_notMem hr, zero_mul]

theorem innerGapPotentialMultiplier_square_inner (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (u v : RadialModeL2 D) :
    ⟪innerGapPotentialMultiplier D hw hpos j
        (innerGapPotentialMultiplier D hw hpos j u), v⟫_ℝ =
      ⟪innerGapPotentialMultiplier D hw hpos j u,
        innerGapPotentialMultiplier D hw hpos j v⟫_ℝ := by
  simpa only [innerGapPotentialMultiplier_adjoint] using
    (innerGapPotentialMultiplier D hw hpos j).adjoint_inner_left v
      (innerGapPotentialMultiplier D hw hpos j u)

end ContinuousFlexibility.Radial
