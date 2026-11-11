import ContinuousFlexibility.Radial.ReferenceGraphInterior
import ContinuousFlexibility.Radial.ReferenceSmoothSourceCalculus
import ContinuousFlexibility.Radial.ReferenceColumnRapid
import ContinuousFlexibility.Radial.ReferenceLeftSwitch

/-!
# Smooth extensions of the reconstructed scalar coefficients

Positive modes extend by zero. For the constant mode, subtracting the
actual left switch reduces the problem to the same zero-extension
theorem. All derivative and forcing estimates come from the original
Jacobi equation and positive attenuation.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open ContinuousFlexibility.Analysis

noncomputable section

theorem ReferenceRapid.const_mul {D : ReferenceData} (hp : RadialPartition D)
    {u : ℝ → ℝ} (hu : ReferenceRapid D u) (c : ℝ) :
    ReferenceRapid D (fun r => c * u r) :=
  hu.mul_moderate hp (ReferenceModerate.const D c)

theorem ReferenceRapid.sub {D : ReferenceData} (hp : RadialPartition D)
    {u v : ℝ → ℝ} (hu : ReferenceRapid D u) (hv : ReferenceRapid D v) :
    ReferenceRapid D (fun r => u r - v r) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hu.add hp (hv.const_mul hp (-1))

theorem reference_jets_rapid_sub_const_mul {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (radialCore D)) (hg : ContDiffOn ℝ ∞ g (radialCore D))
    (hfW : ∀ n, ReferenceRapid D (iteratedDeriv n f))
    (hgW : ∀ n, ReferenceRapid D (iteratedDeriv n g)) (c : ℝ) (n : ℕ) :
    ReferenceRapid D (iteratedDeriv n (fun r => f r - c * g r)) := by
  have hp : RadialPartition D := hD.choose_spec.2.1
  apply ((hfW n).sub hp ((hgW n).const_mul hp c)).of_eqOn
  intro r hr
  have hfn := (hf.contDiffAt (isOpen_Ioo.mem_nhds hr)).of_le
    (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n))
  have hcg : ContDiffOn ℝ ∞ (fun r => c * g r) (radialCore D) :=
    contDiffOn_const.mul hg
  have hcgn := (hcg.contDiffAt (isOpen_Ioo.mem_nhds hr)).of_le
    (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n))
  symm
  rw [iteratedDeriv_fun_sub hfn hcgn, iteratedDeriv_const_mul_field]

theorem referenceCoefficientForcing_jets_rapid {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {U : RadialUnknown} {F : RadialSource} (hF : ReferenceSmoothFiniteSource D F)
    (hcolumn : ∀ k, ReferenceRapid D (iteratedDeriv k (referenceColumn D))) (n k : ℕ) :
    ReferenceRapid D (iteratedDeriv k (referenceCoefficientForcing D U F n)) := by
  unfold referenceCoefficientForcing
  by_cases hn : n = 1
  · simp only [if_pos hn]
    exact reference_jets_rapid_sub_const_mul hD
      (contDiff_referenceRadialCoefficient hF.contDiff n).contDiffOn
      (referenceColumn_contDiff hD.choose_spec.1 hborder).contDiffOn
      (hF.coefficient_jets_rapid hD n) hcolumn U.2 k
  · simpa only [if_neg hn, sub_zero] using
      hF.coefficient_jets_rapid hD n k

theorem referenceRadialCoefficient_output_mean_remainder_ae {D : ReferenceData}
    (hpart : RadialPartition D) {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) :
    referenceRadialCoefficient (outputRemainder D aL U) 0 =ᵐ[volume.restrict (radialCore D)]
      (fun r => referenceRadialCoefficient U.1 0 r - aL * D.chiLeft r) := by
  filter_upwards [hU.1.ae_angular_memLp hpart] with r hr
  have hc : MemLp (fun _ : ℝ => aL * D.chiLeft r) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    memLp_referenceAngular_interval_of_continuous continuous_const
  have he : (fun θ => U.1 (r, θ)) =
      (fun θ => outputRemainder D aL U (r, θ) + aL * D.chiLeft r) := by
    funext θ
    dsimp only [outputRemainder]
    ring
  change referenceAngularCoefficient (fun θ => outputRemainder D aL U (r, θ)) 0 =
    referenceAngularCoefficient (fun θ => U.1 (r, θ)) 0 - aL * D.chiLeft r
  rw [he, referenceAngularCoefficient_add hr hc, referenceAngularCoefficient_const, ite_true]
  ring

theorem radialJacobi_sub_const_mul_on_core {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D)) (hg : ContDiff ℝ ∞ g)
    (J c : ℝ) {r : ℝ} (hr : r ∈ radialCore D) :
    radialJacobi J D.w (fun t => u t - c * g t) r =
      radialJacobi J D.w u r - c * radialJacobi J D.w g r := by
  have hu' : ContDiffOn ℝ ∞ (deriv u) (radialCore D) :=
    hu.deriv_of_isOpen isOpen_Ioo (by simp)
  have hg' : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hder (s : ℝ) (hs : s ∈ radialCore D) :
      deriv (fun t => u t - c * g t) s = deriv u s - c * deriv g s :=
    (((hu.contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt.fun_sub
      ((hg.differentiable (by simp) s).hasDerivAt.const_mul c)).deriv
  have hflux :
      (fun s => D.w s * deriv (fun t => u t - c * g t) s) =ᶠ[𝓝 r]
        (fun s => (D.w s * deriv u s) - c * (D.w s * deriv g s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    rw [hder s hs]
    ring
  have hFu : DifferentiableAt ℝ (fun s => D.w s * deriv u s) r :=
    ((hgeom.2.2.1.1.contDiffAt).mul (hu'.contDiffAt (isOpen_Ioo.mem_nhds hr))).differentiableAt
      (by simp)
  have hFg : DifferentiableAt ℝ (fun s => D.w s * deriv g s) r :=
    (hgeom.2.2.1.1.mul hg').differentiable (by simp) r
  have hd := (hFu.hasDerivAt.fun_sub (hFg.hasDerivAt.const_mul c)).deriv
  unfold radialJacobi
  rw [hflux.deriv_eq, hd]
  ring

/-- The zero mode has a constant left extension and zero right extension,
with its actual weighted remainder supplying all endpoint information. -/
theorem reference_smooth_zeroMode_extension {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {u f : ℝ → ℝ} {aL : ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D)) (hf : ContDiff ℝ ∞ f)
    (he : ∀ r ∈ radialCore D, radialJacobi 0 D.w u r = f r)
    (huW : ReferenceRapid D (fun r => u r - aL * D.chiLeft r))
    (hdW : ReferenceRapid D (deriv u))
    (hfW : ∀ n, ReferenceRapid D (iteratedDeriv n f)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧ EqOn v u (radialCore D) ∧
      (∀ r, r ≤ D.a → v r = aL) ∧ (∀ r, D.b ≤ r → v r = 0) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hp : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨g, hg, ⟨l, h, hal, hlh, hhb, hgl, hgh⟩, hdiff, hgjets, hJjets⟩ :=
    exists_referenceLeftSwitch hD hborder
  let z : ℝ → ℝ := fun r => u r - aL * g r
  let fz : ℝ → ℝ := fun r => f r - aL * radialJacobi 0 D.w g r
  have hz : ContDiffOn ℝ ∞ z (radialCore D) :=
    hu.sub (contDiffOn_const.mul hg.contDiffOn)
  have hJ : ContDiff ℝ ∞ (radialJacobi 0 D.w g) := by
    have h := (contDiff_infty_iff_deriv.mp
      (hgeom.2.2.1.1.mul (contDiff_infty_iff_deriv.mp hg).2)).2
    unfold radialJacobi
    simpa only [zero_mul, zero_div, sub_zero] using h
  have hfz : ContDiff ℝ ∞ fz := hf.sub (contDiff_const.mul hJ)
  have hzW : ReferenceRapid D z := by
    apply (huW.add hp (hdiff.const_mul hp aL)).of_eqOn
    intro r _hr
    dsimp only [z]
    ring
  have hg'W : ReferenceRapid D (deriv g) := by
    simpa only [iteratedDeriv_one] using hgjets 0
  have hdzW : ReferenceRapid D (deriv z) := by
    apply (hdW.sub hp (hg'W.const_mul hp aL)).of_eqOn
    intro r hr
    symm
    exact (((hu.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt.fun_sub
      ((hg.differentiable (by simp) r).hasDerivAt.const_mul aL)).deriv
  have hez : ∀ r ∈ radialCore D, radialJacobi 0 D.w z r = fz r := by
    intro r hr
    change radialJacobi 0 D.w (fun t => u t - aL * g t) r =
      f r - aL * radialJacobi 0 D.w g r
    rw [radialJacobi_sub_const_mul_on_core hgeom hu hg 0 aL hr, he r hr]
  have hfzW (n : ℕ) : ReferenceRapid D (iteratedDeriv n fz) :=
    reference_jets_rapid_sub_const_mul hD hf.contDiffOn hJ.contDiffOn hfW hJjets aL n
  have hzs : ContDiff ℝ ∞ (extendZeroOutside D.a D.b z) :=
    reference_contDiff_zero_extension_of_weighted_jets hD hz
      (reference_radial_jets_rapid hD hz hfz.contDiffOn hez hzW hdzW hfzW)
  refine ⟨fun r => aL * g r + extendZeroOutside D.a D.b z r,
    (contDiff_const.mul hg).add hzs, ?_, ?_, ?_⟩
  · intro r hr
    rw [extendZeroOutside_of_mem hr]
    dsimp only [z]
    ring
  · intro r hr
    rw [hgl r (hr.trans hal.le), extendZeroOutside_of_notMem
      (fun hmem => (not_lt.mpr hr) hmem.1), mul_one, add_zero]
  · intro r hr
    rw [hgh r (hhb.le.trans hr), extendZeroOutside_of_notMem
      (fun hmem => (not_lt.mpr hr) hmem.2), mul_zero, add_zero]

end

end ContinuousFlexibility.Radial
