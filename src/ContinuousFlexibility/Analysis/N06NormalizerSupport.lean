import ContinuousFlexibility.Analysis.SpacesCompactHeights
import ContinuousFlexibility.Analysis.N06FiniteReferenceColumns

/-!
# A genuine normalizer inside the actual normalization region

The normalized reference border is nonzero somewhere in the physical
core. N04 therefore already provides a nonempty open normalization region
there. A smooth transition inside a compact subinterval gives a radial
source of integral one. The exact original height-model decoder realizes
that source, without adding a support assumption on the old psi.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

private theorem n06_open_core_contains_interval {D : ReferenceData}
    {U : Set ℝ} (hU : IsOpen U) (hne : (U ∩ radialCore D).Nonempty) :
    ∃ l h : ℝ, l < h ∧ Icc l h ⊆ U ∩ radialCore D := by
  obtain ⟨r, hrU, hrD⟩ := hne
  have hnb : U ∩ radialCore D ∈ 𝓝 r :=
    (hU.inter isOpen_Ioo).mem_nhds ⟨hrU, hrD⟩
  obtain ⟨l₀, h₀, hr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnb
  obtain ⟨l, hl₀, hlr⟩ := exists_between hr.1
  obtain ⟨h, hrh, hh₀⟩ := exists_between hr.2
  exact ⟨l, h, hlr.trans hrh,
    fun x hx => hsub ⟨hl₀.trans_le hx.1, hx.2.trans_lt hh₀⟩⟩

/-- A radial smooth source of mass one can be placed inside any given
nonempty open subset of the physical core. -/
theorem n06_exists_radial_unit_source_on_open {D : ReferenceData}
    {U : Set ℝ} (hU : IsOpen U) (hne : (U ∩ radialCore D).Nonempty) :
    ∃ g : ℝ → ℝ, ∃ J : Set ℝ,
      ContDiff ℝ ∞ g ∧ IsCompact J ∧ J ⊆ radialCore D ∧ J ⊆ U ∧
      (∀ r, r ∉ J → g r = 0) ∧
      physicalSourceIntegral D (fun p : PolarPoint => g p.1) = 1 := by
  obtain ⟨l, h, hlh, hJ⟩ := n06_open_core_contains_interval hU hne
  have hla : D.a < l := (hJ ⟨le_rfl, hlh.le⟩).2.1
  have hhb : h < D.b := (hJ ⟨hlh.le, le_rfl⟩).2.2
  let χ : ℝ → ℝ := spacesLeftCutoff l h
  have hχ : ContDiff ℝ ∞ χ := spacesLeftCutoff_contDiff l h
  let g : ℝ → ℝ := fun r => -deriv χ r
  have hg : ContDiff ℝ ∞ g := (contDiff_infty_iff_deriv.mp hχ).2.neg
  refine ⟨g, Icc l h, hg, isCompact_Icc,
    fun r hr => (hJ hr).2, fun r hr => (hJ hr).1, ?_, ?_⟩
  · intro r hr
    change -deriv (spacesLeftCutoff l h) r = 0
    rw [spacesLeftCutoff_deriv_eq_zero hlh hr, neg_zero]
  · rw [spaces_physicalSourceIntegral_radial]
    change (∫ r in D.a..D.b, -deriv χ r) = 1
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub
      (fun r _ => hχ.differentiable (by simp) r)
      ((contDiff_infty_iff_deriv.mp hχ).2.continuous.intervalIntegrable D.a D.b)]
    change -(spacesLeftCutoff l h D.b - spacesLeftCutoff l h D.a) = 1
    rw [spacesLeftCutoff_eq_zero hlh hhb.le, spacesLeftCutoff_eq_one hlh hla.le]
    norm_num

theorem n06_normalizationRegion_meets_core
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hborder : RadialTrueBorder D) (h04 : N04Properties D T S C L K base loss ε) :
    (K.normalizationRegion ∩ radialCore D).Nonempty := by
  have hnz : ∃ r : ℝ, referenceColumn D r ≠ 0 := by
    by_contra! hzero
    have he : (fun r => referenceColumn D r * D.phi r) = (fun _ : ℝ => 0) := by
      funext r
      rw [hzero r, zero_mul]
    have hunit := hborder.2.2.2.1
    rw [he, intervalIntegral.integral_zero] at hunit
    exact zero_ne_one hunit
  obtain ⟨r, hr⟩ := hnz
  have hrχ : r ∈ tsupport D.chi :=
    referenceColumn_tsupport_subset (subset_tsupport (referenceColumn D) hr)
  exact ⟨r, h04.1.normalizationSupport hr, (hborder.2.2.1 hrχ).1⟩

/-- The new normalizer belongs to the old height space and is normalized
by the unchanged compatibility functional. Its compact support is proved
to lie inside the actual N04 normalization region. -/
theorem n06_exists_normalizer_in_normalizationRegion
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D) (h04 : N04Properties D T S C L K base loss ε) :
    ∃ ψ : (S.height (3 / 4 : ℝ)).Space, S.Q ψ = 1 ∧
      ∃ g : ℝ → ℝ, ∃ J : Set ℝ,
        ContDiff ℝ ∞ g ∧ IsCompact J ∧ J ⊆ radialCore D ∧
        J ⊆ K.normalizationRegion ∧ (∀ r, r ∉ J → g r = 0) ∧
        (S.height (3 / 4 : ℝ)).decode ψ = fun p : PolarPoint => g p.1 := by
  obtain ⟨g, J, hg, hJ, hJD, hJU, hzero, hunit⟩ :=
    n06_exists_radial_unit_source_on_open h04.1.normalizationOpen (n06_normalizationRegion_meets_core hborder h04)
  have hm : HeightMember D T (3 / 4 : ℝ) (fun p : PolarPoint => g p.1) :=
    spaces_heightMember_of_compact_radial hT hg hJ hJD hzero (3 / 4 : ℝ)
  obtain ⟨ψ, hψ⟩ := (hS.1 (3 / 4 : ℝ)).2.2.2.2.1 (fun p : PolarPoint => g p.1) hm
  refine ⟨ψ, ?_, g, J, hg, hJ, hJD, hJU, hzero, hψ⟩
  exact (hS.2.2.2.2.2.2.2.1 ψ).trans
    ((congrArg (physicalSourceIntegral D) hψ).trans hunit)

end ContinuousFlexibility.Statements
