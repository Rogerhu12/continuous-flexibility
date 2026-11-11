import ContinuousFlexibility.Radial.SelectedTailCauchyUniqueness
import ContinuousFlexibility.Radial.ModeWeakGreen

/-!
# The actual weak modal equation gives the tail Cauchy system

The given half-closed C1 representative supplies the one-sided flux.
On each compact interior interval its weak divergence equation has a
continuous source, so the weak fundamental theorem gives a classical
first-order system. This uses the original radial measure and Robin row.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The homogeneous weak equation has the classical flux derivative at
every point in an interior compact interval. -/
theorem modeLocalEquation_homogeneous_flux_hasDerivAt
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {J : Set ℝ} {U : RadialModePair D} {u : ℝ → ℝ}
    (hEq : ModeLocalEquation D j J U 0) (hscalar : U.2 = 0)
    (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    {a b x : ℝ} (hab : a < b) (hcore : Icc a b ⊆ radialCore D)
    (hJ : Ioo a b ⊆ J) (hu : ContDiffOn ℝ 1 u (Icc a b))
    (hx : x ∈ Ioo a b) :
    HasDerivAt (fun r => D.w r * deriv u r)
      ((j : ℝ) ^ 2 * deriv D.w x / x * u x) x := by
  let g : ℝ → ℝ := fun r => matchingPotential D j r * u r
  have hg : ContinuousOn g (Icc a b) :=
    ((matchingPotential_continuousOn hD j).mono
      (hcore.trans Ioo_subset_Icc_self)).mul hu.continuousOn
  have hsource : matchingPrincipalSource D j U 0 =ᵐ[volume.restrict (Icc a b)] g := by
    have hur := ae_restrict_of_ae_restrict_of_subset hcore
      ((radialHilbertMeasure_ae_iff hD).mp hrep)
    have hz := ae_restrict_of_ae_restrict_of_subset hcore
      ((radialHilbertMeasure_ae_iff hD).mp
        (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)))
    filter_upwards [hur, hz] with r hr hzero
    change matchingPotential D j r * U.1 r +
      U.2 * referenceColumn D r - matchingDensity D r * (0 : RadialModeL2 D) r = g r
    rw [hr, hscalar, hzero]
    simp only [Pi.zero_apply, zero_mul, mul_zero, add_zero, sub_zero, g]
  have hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ r in a..b, u r * deriv (fun t => D.w t * deriv ψ t) r) =
        ∫ r in a..b, g r * ψ r := by
    intro ψ hψ hcψ hsψ
    rw [modeLocalEquation_representative_principal_on_compact hD hB hEq hrep
      hab.le hcore hJ hψ hcψ hsψ]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hsource] with r hr hri
    have hrI : r ∈ Icc a b := by
      simpa only [uIcc_of_le hab.le] using uIoc_subset_uIcc hri
    rw [hr hrI]
  have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab.le
  obtain ⟨hp, _, _⟩ := weakPrincipal_withinFlux_regular hab hu hgi
    (matchingProfileGeometry hD).2.2.1.1 hweak
  have hgax : IntervalIntegrable g volume a x :=
    (hg.mono (fun r hr => ⟨hr.1, hr.2.trans hx.2.le⟩)).intervalIntegrable_of_Icc hx.1.le
  have hgc : ContinuousAt g x :=
    hg.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hgm : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    (hg.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  have hd : HasDerivAt
      (fun r => D.w a * derivWithin u (Icc a b) a + ∫ t in a..r, g t) (g x) x :=
    (intervalIntegral.integral_hasDerivAt_right hgax hgm hgc).const_add
      (D.w a * derivWithin u (Icc a b) a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with r hr
  have hp' := hp r (Ioo_subset_Icc_self hr)
  change D.w r * derivWithin u (Icc a b) r =
    D.w a * derivWithin u (Icc a b) a + ∫ t in a..r, g t at hp'
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)] at hp'
  exact hp'

/-- A half-closed representative of a homogeneous modal weak solution
satisfies the actual value/flux Cauchy system, including the original
one-sided Robin trace at the regular cut. -/
theorem RadialTailCauchyUnique.eq_zero_of_weak
    {D : ReferenceData} {right : Bool} {cut lam : ℝ} {j : ℕ} {v : ℝ × ℝ}
    (hunique : RadialTailCauchyUnique D right cut ((j : ℝ) ^ 2) lam v)
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hcut : cut ∈ radialCore D) {U : RadialModePair D} {u : ℝ → ℝ}
    (hEq : ModeLocalEquation D j (radialTailInterval D right cut) U 0)
    (hscalar : U.2 = 0)
    (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (hu : ContDiffOn ℝ 1 u (radialTailHalf D right cut))
    (hRobin : outerStatePair v (u cut,
      outerTailSign right * D.w cut *
        derivWithin u (radialTailHalf D right cut) cut / lam) = 0) :
    ∀ r ∈ radialTailHalf D right cut, u r = 0 := by
  let s := radialTailHalf D right cut
  let p : ℝ → ℝ := fun r => D.w r * derivWithin u s r
  have hp : ContinuousOn p s :=
    (matchingProfileGeometry hD).2.2.1.1.continuous.continuousOn.mul
      (hu.continuousOn_derivWithin (radialTailHalf_uniqueDiff D right cut) le_rfl)
  have hopen : IsOpen (radialTailInterval D right cut) := by
    cases right <;> exact isOpen_Ioo
  have hsn (r : ℝ) (hr : r ∈ radialTailInterval D right cut) : s ∈ 𝓝 r :=
    Filter.mem_of_superset (hopen.mem_nhds hr) (radialTailInterval_subset_half D right cut)
  have hsys (r : ℝ) (hr : r ∈ radialTailInterval D right cut) :
      HasDerivAt u (p r / D.w r) r ∧
        HasDerivAt p ((j : ℝ) ^ 2 * deriv D.w r / r * u r) r := by
    have hrCore := selectedTailInterval_subset_core hcut right hr
    have hwn := ((matchingProfileGeometry hD).2.2.2.2.1 r hrCore).ne'
    have hd := (hu.differentiableOn (by norm_num) r
      (radialTailInterval_subset_half D right cut hr)).differentiableAt (hsn r hr)
    constructor
    · convert hd.hasDerivAt using 1
      dsimp only [p]
      rw [derivWithin_of_mem_nhds (hsn r hr)]
      field_simp [hwn]
    · have hex : ∃ a b : ℝ, r ∈ Ioo a b ∧
          Icc a b ⊆ radialTailInterval D right cut := by
        cases right
        · change D.a < r ∧ r < cut at hr
          refine ⟨(D.a + r) / 2, (r + cut) / 2, ?_, ?_⟩
          · constructor <;> linarith [hr.1, hr.2]
          · intro t ht
            change D.a < t ∧ t < cut
            constructor <;> linarith [hr.1, hr.2, ht.1, ht.2]
        · change cut < r ∧ r < D.b at hr
          refine ⟨(cut + r) / 2, (r + D.b) / 2, ?_, ?_⟩
          · constructor <;> linarith [hr.1, hr.2]
          · intro t ht
            change cut < t ∧ t < D.b
            constructor <;> linarith [hr.1, hr.2, ht.1, ht.2]
      obtain ⟨a, b, hrI, hI⟩ := hex
      have hg := modeLocalEquation_homogeneous_flux_hasDerivAt hD hB hEq hscalar hrep
        (hrI.1.trans hrI.2) (hI.trans (selectedTailInterval_subset_core hcut right))
        (Ioo_subset_Icc_self.trans hI)
        (hu.mono (hI.trans (radialTailInterval_subset_half D right cut))) hrI
      apply hg.congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hr] with t ht
      dsimp only [p]
      rw [derivWithin_of_mem_nhds (hsn t ht)]
  have hLp : MemLp u 2 ((radialHilbertMeasure D).restrict
      (radialTailInterval D right cut)) :=
    ((memLp_congr_ae hrep).mp (Lp.memLp U.1)).restrict _
  apply hunique u p hu.continuousOn hp hsys hLp
  simpa only [p, s, mul_assoc] using hRobin

end ContinuousFlexibility.Radial
