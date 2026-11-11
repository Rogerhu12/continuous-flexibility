import ContinuousFlexibility.Analysis.N07bReferencePDEDecay
import ContinuousFlexibility.Radial.R11bLeftCorrection
import ContinuousFlexibility.Radial.R11bZeroMode

/-!
# Material decay of the actual compact reference corrections

A continuous radial function supported inside a compact part of the core
has every prescribed height decay, because its quotient by the positive
material height is bounded on that compact set. The existing support
theorems apply this directly to the left-cutoff flux and the actual border
column. The final estimate concerns the genuine reference PDE of a C²
remainder plus the prescribed left constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Compact interior support gives any real height exponent, without an
assumption on the forcing or on a weighted source space. -/
theorem n07b_compact_radial_height_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {J : Set ℝ} (hJ : IsCompact J) (hJcore : J ⊆ radialCore D)
    {g : ℝ → ℝ} (hg : ContinuousOn g J)
    (hzero : ∀ r ∈ radialCore D, r ∉ J → g r = 0) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D, |g r| ≤ C * T.H r ^ γ := by
  have hH : ContinuousOn T.H J :=
    (hT.1 T.H (by simp)).continuousOn.mono hJcore
  have hpow : ContinuousOn (fun r => T.H r ^ γ) J :=
    hH.rpow_const (fun r hr => Or.inl (hT.2.1 r (hJcore hr)).2.1.ne')
  have hratio : ContinuousOn (fun r => g r / T.H r ^ γ) J :=
    hg.div hpow (fun r hr => (Real.rpow_pos_of_pos (hT.2.1 r (hJcore hr)).2.1 γ).ne')
  obtain ⟨B, hB⟩ := hJ.bddAbove_image hratio.abs
  refine ⟨max B 0, le_max_right _ _, fun r hr => ?_⟩
  have hp : 0 < T.H r ^ γ := Real.rpow_pos_of_pos (hT.2.1 r hr).2.1 γ
  by_cases hrJ : r ∈ J
  · have hb : |g r / T.H r ^ γ| ≤ max B 0 :=
      (hB ⟨r, hrJ, rfl⟩).trans (le_max_left _ _)
    rw [abs_div, abs_of_pos hp] at hb
    exact (div_le_iff₀ hp).mp hb
  · rw [hzero r hr hrJ, abs_zero]
    exact mul_nonneg (le_max_right _ _) hp.le

/-- The prescribed left cutoff has genuine compact reference forcing. -/
theorem n07b_chiLeft_flux_height_bound
    {D : ReferenceData} {T : MaterialData}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
      |deriv (fun t => D.w t * deriv D.chiLeft t) r| ≤ C * T.H r ^ γ := by
  obtain ⟨J, hJ, hJcore, hz⟩ := r11b_chiLeft_flux_compact_core hgeom hborder
  exact n07b_compact_radial_height_bound hT hJ hJcore
    (r11b_continuous_chiLeft_flux hgeom hborder).continuousOn hz γ

theorem n07b_chiLeft_referencePDE_height_bound
    {D : ReferenceData} {T : MaterialData}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ annularOpen D,
      |radialPDE D.w (fun r _ => D.chiLeft r) x.1 x.2| ≤ C * T.H x.1 ^ γ := by
  obtain ⟨C, hC, hb⟩ := n07b_chiLeft_flux_height_bound hgeom hT hborder γ
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [r11b_radialPDE_radial]
  exact hb x.1 hx.1

/-- Strict topological support of the actual border cutoff suffices.
No matched representation or inverse is needed. -/
theorem n07b_referenceColumn_height_bound
    {D : ReferenceData} {T : MaterialData}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
      |referenceColumn D r| ≤ C * T.H r ^ γ := by
  refine n07b_compact_radial_height_bound hT hborder.2.1
    (fun r hr => (hborder.2.2.1 hr).1)
    (referenceColumn_contDiff hgeom hborder).continuous.continuousOn ?_ γ
  intro r _ hr
  exact image_eq_zero_of_notMem_tsupport
    (fun hs => hr (referenceColumn_tsupport_subset hs))

/-- The cosine normalization is uniformly bounded in both angle and
frequency, so every actual column mode has the same radial decay. -/
theorem n07b_referenceColumn_cosine_height_bound
    {D : ReferenceData} {T : MaterialData}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) (γ : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ annularOpen D,
      |referenceColumn D x.1 * cosineMode j x.2| ≤ C * T.H x.1 ^ γ := by
  obtain ⟨C, hC, hb⟩ := n07b_referenceColumn_height_bound hgeom hT hborder γ
  refine ⟨C * Real.sqrt 2, mul_nonneg hC (Real.sqrt_nonneg _), fun x hx => ?_⟩
  have hc : |cosineMode j x.2| ≤ Real.sqrt 2 := by
    rw [cosineMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ((j : ℝ) * x.2)) (Real.sqrt_nonneg 2)
  have hp : 0 ≤ C * T.H x.1 ^ γ :=
    mul_nonneg hC (Real.rpow_pos_of_pos (hT.2.1 x.1 hx.1).2.1 γ).le
  rw [abs_mul]
  calc
    _ ≤ (C * T.H x.1 ^ γ) * Real.sqrt 2 :=
      mul_le_mul (hb x.1 hx.1) hc (abs_nonneg _) hp
    _ = _ := by ring

/-- Scalar linearity here is for the actual one-dimensional derivatives. -/
theorem n07b_referencePDE_scaled_cutoff (D : ReferenceData) (a : ℝ)
    (x : PolarPoint) :
    radialPDE D.w (fun r _ => a * D.chiLeft r) x.1 x.2 =
      a * deriv (fun t => D.w t * deriv D.chiLeft t) x.1 := by
  rw [r11b_radialPDE_radial]
  have hflux : (fun t => D.w t * deriv (fun r => a * D.chiLeft r) t) =
      fun t => a * (D.w t * deriv D.chiLeft t) := by
    funext t
    rw [deriv_const_mul_field]
    ring
  rw [hflux, deriv_const_mul_field]

/-- The reference forcing of a remainder plus the prescribed left
constant has its actual compact correction term. -/
theorem n07b_c2_referencePDE_add_cutoff
    {D : ReferenceData} (hgeom : RadialProfileGeometry D)
    (hborder : RadialTrueBorder D) {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ 2 u) (a : ℝ) (x : PolarPoint) :
    radialPDE D.w (fun r θ => u (r, θ) + a * D.chiLeft r) x.1 x.2 =
      radialPDE D.w (fun r θ => u (r, θ)) x.1 x.2 +
        a * deriv (fun t => D.w t * deriv D.chiLeft t) x.1 := by
  have hχ : ContDiff ℝ 2 (fun p : PolarPoint => D.chiLeft p.1) :=
    (hborder.2.2.2.2.1.comp contDiff_fst).of_le (by simp)
  calc
    _ = radialPDE D.w (fun r θ => u (r, θ)) x.1 x.2 +
        radialPDE D.w (fun r _ => a * D.chiLeft r) x.1 x.2 :=
      n07b_c2_radialPDE_add (hgeom.2.2.1.1.differentiable (by simp)) hu
        (contDiff_const.mul hχ) x
    _ = _ := by rw [n07b_referencePDE_scaled_cutoff]

/-- The genuine reference forcing, including the free left constant and
border scalar, has every height exponent below the remainder's jet exponent. -/
theorem n07b_reference_forcing_decay_of_frechet_jets
    {D : ReferenceData} {T : MaterialData}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) {δ γ A K : ℝ}
    (hγδ : γ < δ) (hK : 0 ≤ K) {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n u x‖ ≤ K * T.H x.1 ^ δ * T.M x.1 ^ A)
    (a μ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ annularOpen D,
      |radialPDE D.w (fun r θ => u (r, θ) + a * D.chiLeft r) x.1 x.2 +
        μ * referenceColumn D x.1 * cosineMode 2 x.2| ≤ C * T.H x.1 ^ γ := by
  obtain ⟨C₁, hC₁, hb₁⟩ := n07b_referencePDE_decay_of_frechet_jets hgeom hT hγδ hK hu hjet
  obtain ⟨C₂, hC₂, hb₂⟩ := n07b_chiLeft_flux_height_bound hgeom hT hborder γ
  obtain ⟨C₃, hC₃, hb₃⟩ := n07b_referenceColumn_cosine_height_bound hgeom hT hborder γ 2
  refine ⟨C₁ + |a| * C₂ + |μ| * C₃,
    add_nonneg (add_nonneg hC₁ (mul_nonneg (abs_nonneg _) hC₂))
      (mul_nonneg (abs_nonneg _) hC₃), fun x hx => ?_⟩
  rw [n07b_c2_referencePDE_add_cutoff hgeom hborder hu a x,
    mul_assoc μ (referenceColumn D x.1) (cosineMode 2 x.2)]
  calc
    _ ≤ |radialPDE D.w (fun r θ => u (r, θ)) x.1 x.2| +
        |a * deriv (fun t => D.w t * deriv D.chiLeft t) x.1| +
        |μ * (referenceColumn D x.1 * cosineMode 2 x.2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |radialPDE D.w (fun r θ => u (r, θ)) x.1 x.2| +
        |a| * |deriv (fun t => D.w t * deriv D.chiLeft t) x.1| +
        |μ| * |referenceColumn D x.1 * cosineMode 2 x.2| := by
      rw [abs_mul, abs_mul]
    _ ≤ C₁ * T.H x.1 ^ γ + |a| * (C₂ * T.H x.1 ^ γ) +
        |μ| * (C₃ * T.H x.1 ^ γ) :=
      add_le_add (add_le_add (hb₁ x hx)
        (mul_le_mul_of_nonneg_left (hb₂ x.1 hx.1) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left (hb₃ x hx) (abs_nonneg _))
    _ = _ := by ring

end ContinuousFlexibility.Analysis
