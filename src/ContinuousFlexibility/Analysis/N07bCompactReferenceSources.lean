module

public import ContinuousFlexibility.Analysis.N07bCompactSourceEncoding
public import ContinuousFlexibility.Analysis.N07bReferenceCompatibility
public import ContinuousFlexibility.Radial.ReferenceColumnSmooth
public import ContinuousFlexibility.Radial.R11bZeroMode

/-!
# The actual compact reference corrections as physical sources

Both the cutoff flux derivative and the even reference column have global
smooth representatives, compact radial support strictly inside the core, and
zero physical source integral. They therefore have exact encodings in the
physical source kernel. For the reference cutoff, compactness is proved for
its actual flux on all of the real line; no conclusion about global support
is inferred from a statement restricted to the core.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A cutoff whose derivative is compactly supported gives a compact flux
derivative, with no support condition on the cutoff itself. -/
theorem n07b_cutoffFlux_compact_support
    {D : ReferenceData} {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) :
    HasCompactRadialSupport D
      (fun p => deriv (fun r => D.w r * deriv χ r) p.1) := by
  obtain ⟨K, hK, hKD, _, hz⟩ := hχ.2.2
  have hd : tsupport (deriv χ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro r hr
    by_contra hnot
    exact hr (hz r hnot)
  have hf : tsupport (deriv (fun r => D.w r * deriv χ r)) ⊆ K :=
    tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans hd)
  exact ⟨K, hK, hKD, fun r hr _ =>
    image_eq_zero_of_notMem_tsupport (fun hm => hr (hf hm))⟩

/-- Although the reference cutoff is only prescribed near the two interior
ends, the flat profile makes its flux compactly supported globally. -/
theorem n07b_chiLeftFlux_compact_support
    {D : ReferenceData} (hgeom : RadialProfileGeometry D)
    (hborder : RadialTrueBorder D) :
    HasCompactRadialSupport D
      (fun p => deriv (fun r => D.w r * deriv D.chiLeft r) p.1) := by
  obtain ⟨ε, hε, hleft, hright⟩ := hborder.2.2.2.2.2
  let δ : ℝ := min (ε / 2) ((D.b - D.a) / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith [hgeom.2.1])
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  let J : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hJ : J ⊆ Ioo D.a D.b := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hz : ∀ r, r ∉ J → D.w r * deriv D.chiLeft r = 0 := by
    intro r hrJ
    by_cases hr : r ∈ radialCore D
    · change ¬(D.a + δ ≤ r ∧ r ≤ D.b - δ) at hrJ
      rcases not_and_or.mp hrJ with hL | hR
      · have hrL : r ∈ Ioo D.a (D.a + ε) :=
          ⟨hr.1, by linarith [lt_of_not_ge hL]⟩
        have he : D.chiLeft =ᶠ[𝓝 r] (fun _ : ℝ => 1) := by
          filter_upwards [Ioo_mem_nhds hrL.1 hrL.2] with t ht
          exact hleft t ht
        rw [he.deriv_eq, deriv_const, mul_zero]
      · have hrR : r ∈ Ioo (D.b - ε) D.b :=
          ⟨by linarith [lt_of_not_ge hR], hr.2⟩
        have he : D.chiLeft =ᶠ[𝓝 r] (fun _ : ℝ => 0) := by
          filter_upwards [Ioo_mem_nhds hrR.1 hrR.2] with t ht
          exact hright t ht
        rw [he.deriv_eq, deriv_const, mul_zero]
    · have hout : r ≤ D.a ∨ D.b ≤ r := by
        by_cases ha : D.a < r
        · exact Or.inr (le_of_not_gt (fun hb => hr ⟨ha, hb⟩))
        · exact Or.inl (le_of_not_gt ha)
      rw [hgeom.2.2.1.2 r hout, zero_mul]
  have hflux : tsupport (fun r => D.w r * deriv D.chiLeft r) ⊆ J := by
    apply closure_minimal _ isClosed_Icc
    intro r hr
    by_contra hnot
    exact hr (hz r hnot)
  refine ⟨J, isCompact_Icc, hJ, ?_⟩
  intro r hr θ
  exact image_eq_zero_of_notMem_tsupport
    (fun hm => hr (hflux (tsupport_deriv_subset hm)))

/-- The genuine flux derivative of any global smooth radial field has zero
physical mean, because the profile vanishes at both physical endpoints. -/
theorem n07b_radialFlux_physicalSourceIntegral_eq_zero
    {D : ReferenceData} (hgeom : RadialProfileGeometry D)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    physicalSourceIntegral D
      (fun p => deriv (fun r => D.w r * deriv χ r) p.1) = 0 := by
  have hu : ContDiff ℝ 2 (fun p : PolarPoint => χ p.1) :=
    (hχ.comp contDiff_fst).of_le (by simp)
  have hp : Function.Periodic (fun p : PolarPoint => χ p.1) (0, Real.pi) := by
    intro p
    change χ (p.1 + 0) = χ p.1
    rw [add_zero]
  have h := n07b_reference_physicalSourceIntegral_eq_zero_of_contDiff hgeom hu hp
  change physicalSourceIntegral D
    (fun p => radialPDE D.w (fun r _ => χ r) p.1 p.2) = 0 at h
  simpa only [r11b_radialPDE_radial] using h

/-- Exact source encoding of a smooth radial flux with actual compact support. -/
theorem n07b_exists_radialFlux_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactRadialSupport D
      (fun p => deriv (fun r => D.w r * deriv χ r) p.1)) :
    ∃ F : S.Source,
      (S.height (3 / 4 : ℝ)).decode F.val =
        (fun p => deriv (fun r => D.w r * deriv χ r) p.1) ∧
      ∀ s, S.sourceGrading s F = physicalNorm T (3 / 4 : ℝ) s
        (fun p => deriv (fun r => D.w r * deriv χ r) p.1) := by
  have hdχ : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hf : ContDiff ℝ ∞ (deriv (fun r => D.w r * deriv χ r)) :=
    (contDiff_infty_iff_deriv.mp (hgeom.2.2.1.1.mul hdχ)).2
  apply n07b_exists_source_of_compact_support hT hS (hf.comp contDiff_fst)
  · intro p
    change deriv (fun r => D.w r * deriv χ r) (p.1 + 0) =
      deriv (fun r => D.w r * deriv χ r) p.1
    rw [add_zero]
  · exact fun _ _ => rfl
  · exact hs
  · exact n07b_radialFlux_physicalSourceIntegral_eq_zero hgeom hχ

theorem n07b_exists_chiLeftFlux_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ∃ F : S.Source,
      (S.height (3 / 4 : ℝ)).decode F.val =
        (fun p => deriv (fun r => D.w r * deriv D.chiLeft r) p.1) ∧
      ∀ s, S.sourceGrading s F = physicalNorm T (3 / 4 : ℝ) s
        (fun p => deriv (fun r => D.w r * deriv D.chiLeft r) p.1) :=
  n07b_exists_radialFlux_source hgeom hT hS hborder.2.2.2.2.1
    (n07b_chiLeftFlux_compact_support hgeom hborder)

/-- The physical-spaces cutoff is handled by its own actual support data;
it need not coincide with the reference cutoff. -/
theorem n07b_exists_spacesCutoffFlux_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    ∃ F : S.Source,
      (S.height (3 / 4 : ℝ)).decode F.val =
        (fun p => deriv (fun r => D.w r * deriv S.chiLeft r) p.1) ∧
      ∀ s, S.sourceGrading s F = physicalNorm T (3 / 4 : ℝ) s
        (fun p => deriv (fun r => D.w r * deriv S.chiLeft r) p.1) :=
  n07b_exists_radialFlux_source hgeom hT hS hS.2.2.1.1
    (n07b_cutoffFlux_compact_support hS.2.2.1)

/-- Every scalar multiple of the actual even reference column is a source. -/
theorem n07b_exists_referenceColumn_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (μ : ℝ) :
    ∃ F : S.Source,
      (S.height (3 / 4 : ℝ)).decode F.val =
        (fun p => μ * referenceColumn D p.1 * cosineMode 2 p.2) ∧
      ∀ s, S.sourceGrading s F = physicalNorm T (3 / 4 : ℝ) s
        (fun p => μ * referenceColumn D p.1 * cosineMode 2 p.2) := by
  have hf : ContDiff ℝ ∞ (fun p : PolarPoint =>
      μ * referenceColumn D p.1 * cosineMode 2 p.2) :=
    (contDiff_const.mul ((referenceColumn_contDiff hgeom hborder).comp contDiff_fst)).mul
      ((r11b_contDiff_cosineMode 2).comp contDiff_snd)
  apply n07b_exists_source_of_compact_support hT hS hf
  · intro p
    change μ * referenceColumn D (p.1 + 0) * cosineMode 2 (p.2 + Real.pi) = _
    rw [add_zero]
    have hp : cosineMode 2 (p.2 + Real.pi) = cosineMode 2 p.2 := by
      simpa only [Nat.mul_one] using cosineMode_even_frequency_periodic 1 p.2
    rw [hp]
  · intro r θ
    simp only [cosineMode, mul_neg, Real.cos_neg]
  · refine ⟨tsupport D.chi, hborder.2.1,
      fun r hr => (hborder.2.2.1 hr).1, ?_⟩
    intro r hr θ
    have hz : referenceColumn D r = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hm => hr (referenceColumn_tsupport_subset hm))
    change μ * referenceColumn D r * cosineMode 2 θ = 0
    rw [hz, mul_zero, zero_mul]
  · exact n07b_referenceColumn_physicalSourceIntegral_eq_zero D μ

end ContinuousFlexibility.Analysis
