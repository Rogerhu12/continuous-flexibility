import ContinuousFlexibility.Radial.InnerGapDirichletSupport
import ContinuousFlexibility.Radial.InnerRadialL2Pairing
import ContinuousFlexibility.Radial.InnerRadialGreen

/-!
# The actual differential equation of the closed positive-gap inverse

The energy coordinates give the physical bilinear radial form.
Integration by parts on the smooth zero-Dirichlet core passes to its
closure as an equality of continuous linear functionals. Consequently
the arbitrary-L² inverse satisfies the actual radial weak equation;
the form construction is not an unrelated abstract graph.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

def innerGapEnergyBilinear (w : ℝ → ℝ) (j a b : ℝ) (u v : ℝ → ℝ) : ℝ :=
  ∫ r in a..b, w r * deriv u r * deriv v r + j ^ 2 * deriv w r / r * u r * v r

theorem innerGapEnergy_weighted_product {r j : ℝ} {w u v : ℝ → ℝ}
    (hr : 0 < r) (hw : 0 < w r) (hslope : 0 ≤ r * deriv w r / w r) :
    (12 * w r / r ^ 2) * innerGapGradientField u r * innerGapGradientField v r +
        (12 * w r / r ^ 2) * innerGapPotentialField w j u r * innerGapPotentialField w j v r =
      w r * deriv u r * deriv v r + j ^ 2 * deriv w r / r * u r * v r := by
  have hα : 0 ≤ (j ^ 2 / 12) * (r * deriv w r / w r) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hslope
  have hg : (12 * w r / r ^ 2) * (r / Real.sqrt 12) ^ 2 = w r := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
    field_simp [hr.ne'] <;> ring
  have hp : (12 * w r / r ^ 2) *
      Real.sqrt ((j ^ 2 / 12) * (r * deriv w r / w r)) ^ 2 =
        j ^ 2 * deriv w r / r := by
    rw [Real.sq_sqrt hα]
    field_simp [hr.ne', hw.ne'] <;> ring
  calc
    _ = ((12 * w r / r ^ 2) * (r / Real.sqrt 12) ^ 2) * (deriv u r * deriv v r) +
        ((12 * w r / r ^ 2) *
          Real.sqrt ((j ^ 2 / 12) * (r * deriv w r / w r)) ^ 2) * (u r * v r) := by
      unfold innerGapGradientField innerGapPotentialField
      ring
    _ = _ := by rw [hg, hp]; ring

theorem innerGapEnergyPair_inner (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (u v : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ⟪innerGapEnergyPair D hw ha hcore hpos j u hu,
      innerGapEnergyPair D hw ha hcore hpos j v hv⟫_ℝ =
      innerGapEnergyBilinear D.w j a b u v := by
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    innerGapEnergyPair_fst, innerGapEnergyPair_snd]
  rw [innerRadialIntervalToLp_inner D hw.continuous hab,
    innerRadialIntervalToLp_inner D hw.continuous hab]
  have hρ := innerRadialGapDensity_continuousOn (b := b) ha hw.continuous
  have hdu : ContinuousOn (innerGapGradientField u) (Icc a b) :=
    (innerGapGradientField_continuous hu).continuousOn
  have hdv : ContinuousOn (innerGapGradientField v) (Icc a b) :=
    (innerGapGradientField_continuous hv).continuousOn
  have hqu := innerGapPotentialField_continuousOn hw hu hpos j
  have hqv := innerGapPotentialField_continuousOn hw hv hpos j
  unfold innerGapEnergyBilinear
  rw [← intervalIntegral.integral_add
    (((hρ.mul hdu).mul hdv).intervalIntegrable_of_Icc hab)
    (((hρ.mul hqu).mul hqv).intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
  exact innerGapEnergy_weighted_product (ha.trans_le hr'.1) (hpos r hr') (hslope r hr')

/-- Actual integration by parts, retaining both endpoint terms. -/
theorem innerGapEnergyBilinear_boundary {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w u v : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    innerGapEnergyBilinear w j a b u v =
      u b * (w b * deriv v b) - u a * (w a * deriv v a) -
        (∫ r in a..b, u r * radialJacobi (j ^ 2) w v r) := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hdv := (contDiff_infty_iff_deriv.mp hv).2
  have hflux := hw.mul hdv
  have hdflux := (contDiff_infty_iff_deriv.mp hflux).2
  have hc : Continuous (fun r => deriv u r * (w r * deriv v r) +
      u r * deriv (fun t => w t * deriv v t) r) :=
    (hdu.continuous.mul hflux.continuous).add (hu.continuous.mul hdflux.continuous)
  have hderiv (r : ℝ) : HasDerivAt (fun t => u t * (w t * deriv v t))
      (deriv u r * (w r * deriv v r) + u r * deriv (fun t => w t * deriv v t) r) r :=
    (hu.differentiable (by simp) r).hasDerivAt.mul
      (hflux.differentiable (by simp) r).hasDerivAt
  have hFTC : (∫ r in a..b, deriv u r * (w r * deriv v r) +
      u r * deriv (fun t => w t * deriv v t) r) =
        u b * (w b * deriv v b) - u a * (w a * deriv v a) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r ∈ uIcc a b) => hderiv r) (hc.intervalIntegrable a b)
  have hL := (hu.continuous.continuousOn.mul
    (innerRadialJacobi_continuousOn (j := j) ha hw hv)).intervalIntegrable_of_Icc hab
  calc
    _ = (∫ r in a..b, deriv u r * (w r * deriv v r) +
        u r * deriv (fun t => w t * deriv v t) r) -
      (∫ r in a..b, u r * radialJacobi (j ^ 2) w v r) := by
      unfold innerGapEnergyBilinear
      rw [← intervalIntegral.integral_sub (hc.intervalIntegrable a b) hL]
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      unfold radialJacobi
      ring
    _ = _ := by rw [hFTC]

theorem innerGapEnergyBilinear_green {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w u v : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hua : u a = 0) (hub : u b = 0) :
    innerGapEnergyBilinear w j a b u v =
      -(∫ r in a..b, u r * radialJacobi (j ^ 2) w v r) := by
  simpa only [hua, hub, zero_mul, sub_self, zero_sub] using
    innerGapEnergyBilinear_boundary hab ha hw hu hv

/-- The actual normalized differential expression applied to a test. -/
def innerGapTestSource (w : ℝ → ℝ) (j : ℝ) (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(r ^ 2 / (12 * w r)) * radialJacobi (j ^ 2) w φ r

theorem innerGapTestSource_continuousOn {a b : ℝ} (ha : 0 < a)
    {w φ : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ r ∈ Icc a b, 0 < w r) (j : ℝ) :
    ContinuousOn (innerGapTestSource w j φ) (Icc a b) :=
  (((continuous_id.pow 2).continuousOn.div
    (continuous_const.mul hw.continuous).continuousOn
      (fun r hr => mul_ne_zero (by norm_num) (hpos r hr).ne')).neg).mul
        (innerRadialJacobi_continuousOn (j := j) ha hw hφ)

theorem innerGapTestSource_pairing (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (u φ : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (hφ : ContDiff ℝ ∞ φ) :
    ⟪innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn,
      innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapTestSource D.w j φ)
        (innerGapTestSource_continuousOn ha hw hφ hpos j)⟫_ℝ =
      -(∫ r in a..b, u r * radialJacobi (j ^ 2) D.w φ r) := by
  rw [innerRadialIntervalToLp_inner D hw.continuous hab, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
  dsimp only [innerGapTestSource]
  field_simp [(ha.trans_le hr'.1).ne', (hpos r hr').ne'] <;> ring

/-- The true radial Green identity extends to the entire closed
Dirichlet form domain, including arbitrary L² solution witnesses. -/
theorem innerGapFormSpace_green_test (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) :
    ⟪q.snd, innerGapEnergyPair D hw ha hcore hpos j φ hφ⟫_ℝ =
      ⟪q.fst, innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapTestSource D.w j φ)
        (innerGapTestSource_continuousOn ha hw hφ hpos j)⟫_ℝ := by
  let Aφ := innerRadialIntervalToLp D hw.continuous ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapTestSource D.w j φ)
    (innerGapTestSource_continuousOn ha hw hφ hpos j)
  let Eφ := innerGapEnergyPair D hw ha hcore hpos j φ hφ
  have hf : Continuous (fun q : InnerGapEnergyTriple D => q.fst) :=
    (WithLp.fstL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hg : Continuous (fun q : InnerGapEnergyTriple D => q.snd) :=
    (WithLp.sndL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hclosed : IsClosed {q : InnerGapEnergyTriple D | ⟪q.snd, Eφ⟫_ℝ = ⟪q.fst, Aφ⟫_ℝ} :=
    isClosed_eq (hg.inner continuous_const) (hf.inner continuous_const)
  apply (closure_minimal ?_ hclosed) ((mem_innerGapFormSpace D j a b q).mp hq)
  rintro r ⟨u, hu, _, hsu, hu₀, hu₁, hu₂⟩
  have hvalue : r.fst = innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn :=
    Lp.ext (hu₀.trans (innerRadialIntervalToLp_ae D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn).symm)
  have hgrad : r.snd.fst = (innerGapEnergyPair D hw ha hcore hpos j u hu).fst :=
    Lp.ext (hu₁.trans (innerGapEnergyPair_fst_ae D hw ha hcore hpos j u hu).symm)
  have hpot : r.snd.snd = (innerGapEnergyPair D hw ha hcore hpos j u hu).snd :=
    Lp.ext (hu₂.trans (innerGapEnergyPair_snd_ae D hw ha hcore hpos j u hu).symm)
  have henergy : r.snd = innerGapEnergyPair D hw ha hcore hpos j u hu := by
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ (RadialModeL2 D) (RadialModeL2 D)).injective
    apply Prod.ext
    · simpa only [WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_fst] using hgrad
    · simpa only [WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_snd] using hpot
  have hua : u a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hsu h).1)
  have hub : u b = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl b) (hsu h).2)
  dsimp only [Set.mem_setOf_eq, Eφ, Aφ]
  rw [hvalue, henergy, innerGapEnergyPair_inner D hw hab ha hcore hpos hslope,
    innerGapEnergyBilinear_green hab ha hw hu hφ hua hub,
    innerGapTestSource_pairing D hw hab ha hcore hpos]

theorem innerGapFormGraph_weak_pairing (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    {u f : RadialModeL2 D} (h : InnerGapFormGraph D j a b u f)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    ⟪u, innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapTestSource D.w j φ)
        (innerGapTestSource_continuousOn ha hw hφ hpos j)⟫_ℝ =
      ⟪f, innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) φ hφ.continuous.continuousOn⟫_ℝ := by
  obtain ⟨q, hq, hvalue, hform⟩ := (innerGapFormGraph_iff D j a b u f).mp h
  let test : InnerGapEnergyTriple D := WithLp.toLp 2
    (innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) φ hφ.continuous.continuousOn,
      innerGapEnergyPair D hw ha hcore hpos j φ hφ)
  have ht : test ∈ innerGapFormSpace D j a b :=
    (mem_innerGapFormSpace D j a b test).mpr
      (subset_closure (innerGapEnergyTriple_mem_core D hw ha hcore hpos j φ hφ hcφ hsφ))
  have hg := innerGapFormSpace_green_test D hw hab ha hcore hpos hslope j φ hφ q hq
  rw [hvalue] at hg
  exact hg.symm.trans (by
    simpa only [test, WithLp.toLp_fst, WithLp.toLp_snd] using (hform test ht).symm)

/-- The actual radial weak equation for arbitrary physical L² forcing. -/
theorem innerGapFormGraph_radial_weak (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    {u f : RadialModeL2 D} (h : InnerGapFormGraph D j a b u f)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    (∫ r in Ioo a b, u r * radialJacobi (j ^ 2) D.w φ r) =
      -(∫ r in Ioo a b, (12 * D.w r / r ^ 2) * f r * φ r) := by
  have he := innerGapFormGraph_weak_pairing D hw hab ha hcore hpos hslope h φ hφ hcφ hsφ
  rw [innerRadialIntervalToLp_inner_right, innerRadialIntervalToLp_inner_right] at he
  have hi : (∫ r in Ioo a b, (12 * D.w r / r ^ 2) * u r * innerGapTestSource D.w j φ r) =
      -(∫ r in Ioo a b, u r * radialJacobi (j ^ 2) D.w φ r) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only [innerGapTestSource]
    field_simp [(ha.trans hr.1).ne', (hpos r (Ioo_subset_Icc_self hr)).ne'] <;> ring
  rw [hi] at he
  linarith only [he]


theorem innerGapDirichletInverse_radial_weak (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (f : RadialModeL2 D) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Ioo a b) :
    (∫ r in Ioo a b,
      innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope f r *
        radialJacobi (j ^ 2) D.w φ r) =
      -(∫ r in Ioo a b, (12 * D.w r / r ^ 2) * f r * φ r) :=
  innerGapFormGraph_radial_weak D hw hab ha hcore hpos
    (fun r hr => hs.le.trans (hslope r hr))
    (innerGapDirichletInverse_graph D hw hab ha hj hs hcore hpos hslope f) φ hφ hcφ hsφ

end ContinuousFlexibility.Radial
