import ContinuousFlexibility.Radial.SelectedWholeWeakInverse
import ContinuousFlexibility.Radial.ModeWeakLinearity
import ContinuousFlexibility.Analysis.L2RestrictionSplit

/-!
# The constructed exterior inverse in the original radial coordinate

Reflection is applied simultaneously to the actual measure, operator,
test function and Jacobi test source. The resulting bounded operator on
the radial tail has the full ordinary-support weak pairing.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem outerRegionEquiv_ae_of_ae {D : ReferenceData} {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D)
    {f : Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))}
    {u : ℝ → ℝ}
    (hf : (f : ℝ → ℝ) =ᵐ[outerOutwardIntervalMeasure D right
      (radialTailInterval D right cut)] u) :
    (outerRegionEquiv hcut f : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (radialTailInterval D right cut)]
        fun r => u (outerOutwardRadius right r) := by
  have hf' : (f : ℝ → ℝ) =ᵐ[Measure.map (outerOutwardRadius right)
      ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))] u := by
    rwa [← outerOutwardRegionMeasure_eq_map hcut]
  exact (outerRegionEquiv_ae hcut f).trans
    (ae_eq_comp (measurableEmbedding_outerOutwardRadius right).measurable.aemeasurable hf')

def outerRadialRegionOperator {D : ReferenceData} {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D)
    (R : Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))) :
    Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) :=
  (outerRegionEquiv hcut).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (R.comp (outerRegionEquiv hcut).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem outerRadialRegionOperator_apply {D : ReferenceData} {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D)
    (R : Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)))
    (f : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))) :
    outerRadialRegionOperator hcut R f =
      outerRegionEquiv hcut (R ((outerRegionEquiv hcut).symm f)) := rfl

theorem outerRadialRegionOperator_test_pairing
    {D : ReferenceData} (hD : IsAccumulatingProfile D) {right : Bool} {cut lam : ℝ}
    (hcut : cut ∈ radialCore D) (hlam : lam ≠ 0) {j : ℕ} {v : ℝ × ℝ}
    {R : Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))}
    (hR : OuterWeightedGreenResponse
      (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))
      (outerTailOutwardWeight D right) (selectedOutwardDensity D right)
      (outerTailSign right * cut) (outerTailSign right * tailPhysicalEndpoint D right)
      ((j : ℝ) ^ 2) lam v R)
    (hunique : OuterWeightedHomogeneousUnique
      (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))
      (outerTailOutwardWeight D right) (outerTailSign right * cut)
      (outerTailSign right * tailPhysicalEndpoint D right) ((j : ℝ) ^ 2) lam v)
    (hsym : R.toLinearMap.IsSymmetric)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : Function.support ψ ⊆ radialTailInterval D right cut)
    (f : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))) :
    ⟪outerRadialRegionOperator hcut R f,
      l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)
        (matchingJacobiVector D hD j ψ hψ)⟫_ℝ =
      -⟪f, l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)
        (matchingSmoothVector D hD ψ hψ)⟫_ℝ := by
  let E := outerRegionEquiv (right := right) hcut
  let φ : ℝ → ℝ := fun x => ψ (outerOutwardRadius right x)
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_outerOutwardRadius right)
  have hsφ : Function.support φ ⊆ Ioo (outerTailSign right * cut)
      (outerTailSign right * tailPhysicalEndpoint D right) := by
    intro x hx
    have hi : x ∈ outerOutwardRadius right '' radialTailInterval D right cut :=
      ⟨outerOutwardRadius right x, hs hx, outerOutwardRadius_twice right x⟩
    simpa only [outerOutward_tail_image, outerOutwardRadius_eq_sign] using hi
  have hφLp := selectedOutwardSmooth_memLp (right := right) hD hcut hφ
  have hJLp := selectedOutwardJacobiTest_memLp (right := right) hD hcut hφ j
  let p := hφLp.toLp φ
  let q := hJLp.toLp (selectedOutwardJacobiTest D right j φ)
  have hep : E p = l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)
      (matchingSmoothVector D hD ψ hψ) := by
    have hg : (matchingSmoothVector D hD ψ hψ : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ψ :=
      MemLp.coeFn_toLp _
    apply Lp.ext
    filter_upwards [outerRegionEquiv_ae_of_ae hcut hφLp.coeFn_toLp,
      l2Restrict_coeFn (radialHilbertMeasure D) (radialTailInterval D right cut)
        (matchingSmoothVector D hD ψ hψ), ae_restrict_of_ae hg] with r hr hs hψr
    simpa only [φ, outerOutwardRadius_twice, hs, hψr] using hr
  have heq : E q = l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)
      (matchingJacobiVector D hD j ψ hψ) := by
    have hg : (matchingJacobiVector D hD j ψ hψ : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        matchingJacobiTest D j ψ := MemLp.coeFn_toLp _
    apply Lp.ext
    filter_upwards [outerRegionEquiv_ae_of_ae hcut hJLp.coeFn_toLp,
      l2Restrict_coeFn (radialHilbertMeasure D) (radialTailInterval D right cut)
        (matchingJacobiVector D hD j ψ hψ), ae_restrict_of_ae hg] with r hr hs hψr
    simpa only [φ, selectedOutwardJacobiTest, radialJacobi_outward_pullback,
      outerOutwardRadius_twice, selectedOutwardDensity_reflect, matchingJacobiTest,
      hs, hψr] using hr
  have hg := matchingProfileGeometry hD
  have hab : outerTailSign right * cut < outerTailSign right * tailPhysicalEndpoint D right := by
    cases right
    · simpa [outerTailSign, tailPhysicalEndpoint] using neg_lt_neg hcut.1
    · simpa [outerTailSign, tailPhysicalEndpoint] using hcut.2
  have hw : ContDiff ℝ ∞ (outerTailOutwardWeight D right) :=
    hg.2.2.1.1.comp (contDiff_const.mul contDiff_id)
  have hcore (x : ℝ) (hx : x ∈ Ico (outerTailSign right * cut)
      (outerTailSign right * tailPhysicalEndpoint D right)) :
      outerOutwardRadius right x ∈ radialCore D :=
    outerOutwardRadius_mem_core hcut (by simpa only [outerOutwardRadius_eq_sign] using hx)
  have hwn (x : ℝ) (hx : x ∈ Ico (outerTailSign right * cut)
      (outerTailSign right * tailPhysicalEndpoint D right)) :
      outerTailOutwardWeight D right x ≠ 0 := by
    change D.w (outerTailSign right * x) ≠ 0
    rw [← outerOutwardRadius_eq_sign]
    exact (hg.2.2.2.2.1 _ (hcore x hx)).ne'
  have hrn (x : ℝ) (hx : x ∈ Ico (outerTailSign right * cut)
      (outerTailSign right * tailPhysicalEndpoint D right)) : x ≠ 0 := by
    have hp := hg.1.trans (hcore x hx).1
    intro hx0
    rw [hx0, outerOutwardRadius_eq_sign, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have hpair : ⟪R (E.symm f), q⟫_ℝ = -⟪E.symm f, p⟫_ℝ := by
    apply hR.test_pairing hunique hsym hab hlam hw hwn hrn
    · intro q
      simpa only [outerOutwardRadius_eq_sign] using
        (outerOutwardRegion_ae_iff hD hcut (p := q))
    · intro x hx
      refine (selectedOutwardDensity_pos (right := right) hD hcut x ?_).ne'
      simpa only [outerOutwardRadius_eq_sign] using Ioo_subset_Ico_self hx
    · exact hφ
    · exact hsφ
  rw [outerRadialRegionOperator_apply, ← heq, E.inner_map_map, hpair,
    ← E.inner_map_map (E.symm f) p, E.apply_symm_apply, hep]

end ContinuousFlexibility.Radial
