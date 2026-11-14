module

public import ContinuousFlexibility.Analysis.N07aOpenIntervalPointwise
public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# The four true L¹ jets controlling an interior point of an open strip

All uses of the fundamental theorem take place in an interior compact
rectangle. The constants depend only on its radial length.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff ENNReal

theorem n07a_radialSlice_deriv_of_contDiffAt {g : PolarPoint → ℝ} {x θ : ℝ}
    (hg : ContDiffAt ℝ ∞ g (x, θ)) :
    deriv (fun r : ℝ => g (r, θ)) x = radialPartial g (x, θ) :=
  ((hg.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x θ))).deriv

theorem n07a_angularSlice_deriv_of_contDiffAt {g : PolarPoint → ℝ} {x θ : ℝ}
    (hg : ContDiffAt ℝ ∞ g (x, θ)) :
    deriv (fun t : ℝ => g (x, t)) θ = angularPartial g (x, θ) :=
  ((hg.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ x).prodMk (hasDerivAt_id θ))).deriv

theorem n07a_integrableOn_inner_rectangle {A B a b : ℝ} {g : PolarPoint → ℝ}
    (hg : ContinuousOn g (Ioo A B ×ˢ (univ : Set ℝ))) (ha : A < a) (hb : b < B) :
    IntegrableOn g (Ioc a b ×ˢ Ioc 0 Real.pi) volume := by
  have hsub : Icc a b ×ˢ Icc (0 : ℝ) Real.pi ⊆ Ioo A B ×ˢ (univ : Set ℝ) :=
    fun _ hp => ⟨⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb⟩, mem_univ _⟩
  exact ((hg.mono hsub).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem n07a_openStrip_angle_slice_L1 {A B a b x : ℝ} {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioo A B ×ˢ (univ : Set ℝ)))
    (ha : A < a) (hb : b < B) (hab : a < b) (hx : x ∈ Icc a b) :
    (∫ θ in Ioc 0 Real.pi, |g (x, θ)|) ≤
      (b - a)⁻¹ * (∫ p in Ioc a b ×ˢ Ioc 0 Real.pi, |g p|) +
        ∫ p in Ioc a b ×ˢ Ioc 0 Real.pi, |radialPartial g p| := by
  let μ := volume.restrict (Ioc a b)
  let ν := volume.restrict (Ioc (0 : ℝ) Real.pi)
  have hmeasure : μ.prod ν = volume.restrict (Ioc a b ×ˢ Ioc (0 : ℝ) Real.pi) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hgr : ContDiffOn ℝ ∞ (radialPartial g) (Ioo A B ×ˢ (univ : Set ℝ)) :=
    (hg.fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) (by simp)).clm_apply
      contDiffOn_const
  have hi : Integrable (fun p => |g p|) (μ.prod ν) := by
    rw [hmeasure]
    exact n07a_integrableOn_inner_rectangle hg.continuousOn.abs ha hb
  have hid : Integrable (fun p => |radialPartial g p|) (μ.prod ν) := by
    rw [hmeasure]
    exact n07a_integrableOn_inner_rectangle hgr.continuousOn.abs ha hb
  have hxin : x ∈ Ioo A B := ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hslice : Integrable (fun θ => |g (x, θ)|) ν :=
    ((hg.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun _ => ⟨hxin, mem_univ _⟩)).continuous.abs).integrableOn_Ioc
  have hpoint (θ : ℝ) : |g (x, θ)| ≤
      (b - a)⁻¹ * (∫ r, |g (r, θ)| ∂μ) + ∫ r, |radialPartial g (r, θ)| ∂μ := by
    have hgt : ContDiffOn ℝ ∞ (fun r : ℝ => g (r, θ)) (Ioo A B) :=
      hg.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun _ hr => ⟨hr, mem_univ _⟩)
    have h := n07a_abs_le_openInterval_average_add_deriv hgt ha hb hab hx
    have he : (∫ r in Ioc a b, |deriv (fun t : ℝ => g (t, θ)) r|) =
        ∫ r, |radialPartial g (r, θ)| ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [n07a_radialSlice_deriv_of_contDiffAt
        (hg.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
          ⟨⟨ha.trans hr.1, hr.2.trans_lt hb⟩, mem_univ _⟩))]
    rw [he] at h
    exact h
  have h := integral_mono hslice
    ((hi.integral_prod_right.const_mul _).add hid.integral_prod_right) hpoint
  change (∫ θ, |g (x, θ)| ∂ν) ≤
    ∫ θ, ((b - a)⁻¹ * (∫ r, |g (r, θ)| ∂μ) +
      ∫ r, |radialPartial g (r, θ)| ∂μ) ∂ν at h
  rw [integral_add (hi.integral_prod_right.const_mul _) hid.integral_prod_right,
    integral_const_mul, ← integral_prod_symm (fun p => |g p|) hi,
    ← integral_prod_symm (fun p => |radialPartial g p|) hid, hmeasure] at h
  exact h

theorem n07a_openStrip_pointwise_L1 {A B a b x θ : ℝ} {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioo A B ×ˢ (univ : Set ℝ)))
    (ha : A < a) (hb : b < B) (hab : a < b) (hx : x ∈ Icc a b)
    (hθ : θ ∈ Icc 0 Real.pi) :
    |g (x, θ)| ≤ (1 + (b - a)⁻¹) *
      ((∫ p in Ioc a b ×ˢ Ioc 0 Real.pi, |g p|) +
        (∫ p in Ioc a b ×ˢ Ioc 0 Real.pi, |radialPartial g p|) +
        (∫ p in Ioc a b ×ˢ Ioc 0 Real.pi, |angularPartial g p|) +
        ∫ p in Ioc a b ×ˢ Ioc 0 Real.pi, |radialPartial (angularPartial g) p|) := by
  have hxin : x ∈ Ioo A B := ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hgx : ContDiff ℝ ∞ (fun t : ℝ => g (x, t)) :=
    hg.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ⟨hxin, mem_univ _⟩)
  have h := abs_le_interval_average_add_deriv hgx Real.pi_pos hθ
  have he : (fun t : ℝ => deriv (fun u : ℝ => g (x, u)) t) =
      (fun t => angularPartial g (x, t)) := by
    funext t
    exact n07a_angularSlice_deriv_of_contDiffAt
      (hg.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hxin, mem_univ _⟩))
  simp only [sub_zero, he] at h
  have hπ : Real.pi⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [Real.one_le_pi_div_two])
  have hθg : ContDiffOn ℝ ∞ (angularPartial g) (Ioo A B ×ˢ (univ : Set ℝ)) :=
    (hg.fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) (by simp)).clm_apply
      contDiffOn_const
  have hfirst := n07a_openStrip_angle_slice_L1 hg ha hb hab hx
  have hsecond := n07a_openStrip_angle_slice_L1 hθg ha hb hab hx
  have htop : |g (x, θ)| ≤
      (∫ t in Ioc 0 Real.pi, |g (x, t)|) +
        ∫ t in Ioc 0 Real.pi, |angularPartial g (x, t)| :=
    h.trans (add_le_add
      ((mul_le_mul_of_nonneg_right hπ (integral_nonneg (fun _ => abs_nonneg _))).trans_eq
        (one_mul _)) le_rfl)
  apply (htop.trans (add_le_add hfirst hsecond)).trans
  have h0 : 0 ≤ ∫ p in Ioc a b ×ˢ Ioc (0 : ℝ) Real.pi, |g p| := integral_nonneg
    (fun p => abs_nonneg (g p))
  have hr : 0 ≤ ∫ p in Ioc a b ×ˢ Ioc (0 : ℝ) Real.pi, |radialPartial g p| := integral_nonneg
    (fun p => abs_nonneg (radialPartial g p))
  have ht : 0 ≤ ∫ p in Ioc a b ×ˢ Ioc (0 : ℝ) Real.pi, |angularPartial g p| := integral_nonneg
    (fun p => abs_nonneg (angularPartial g p))
  have hrt : 0 ≤ ∫ p in Ioc a b ×ˢ Ioc (0 : ℝ) Real.pi, |radialPartial (angularPartial g) p| :=
    integral_nonneg
    (fun p => abs_nonneg (radialPartial (angularPartial g) p))
  have hl : 0 ≤ (b - a)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hab).le
  nlinarith [mul_nonneg hl hr, mul_nonneg hl hrt]

end ContinuousFlexibility.Analysis
