import ContinuousFlexibility.Radial.R11bTestPairing
import ContinuousFlexibility.Radial.RadialHeight
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiating the actual radial tests

Constant directional derivatives preserve smoothness, angular periodicity,
and compact radial support.  The actual radial operator applied to a test is
continuous and has the same compact radial support, so its pairing with a
locally physical L² output is an actual integrable function.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_contDiff_directionalPartial {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (d : PolarPoint) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ ψ p d) :=
  contDiffOn_univ.mp
    ((hψ.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)).clm_apply contDiffOn_const)

theorem r11b_periodic_directionalPartial {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {v : PolarPoint} (hper : Function.Periodic ψ v)
    (d : PolarPoint) : Function.Periodic (fun p => fderiv ℝ ψ p d) v := by
  intro p
  have hd : HasFDerivAt (fun q : PolarPoint => ψ (q + v))
      (fderiv ℝ ψ (p + v)) p := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
      ((hψ.differentiable (by simp) (p + v)).hasFDerivAt.comp p
        ((hasFDerivAt_id p).add_const v))
  have heq : (fun q : PolarPoint => ψ (q + v)) = ψ := funext hper
  rw [heq] at hd
  exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L d) hd.fderiv.symm

theorem r11b_directionalPartial_zero_outside {K : Set ℝ} (hK : IsClosed K)
    {ψ : PolarPoint → ℝ} (hzero : ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0)
    (d : PolarPoint) {r : ℝ} (hr : r ∉ K) (θ : ℝ) :
    fderiv ℝ ψ (r, θ) d = 0 := by
  have hopen : IsOpen {p : PolarPoint | p.1 ∉ K} :=
    hK.isOpen_compl.preimage continuous_fst
  have heq : ψ =ᶠ[𝓝 (r, θ)] (fun _ : PolarPoint => 0) := by
    filter_upwards [hopen.mem_nhds hr] with p hp
    exact hzero p.1 hp p.2
  rw [heq.fderiv_eq (𝕜 := ℝ)]
  simp only [fderiv_const, zero_apply]

theorem r11b_radialTest_directionalPartial {D : ReferenceData}
    {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) (d : PolarPoint) :
    RadialTest D (fun p => fderiv ℝ ψ p d) := by
  refine ⟨r11b_contDiff_directionalPartial hψ.1 d,
    r11b_periodic_directionalPartial hψ.1 hψ.2.1 d, ?_⟩
  obtain ⟨K, hK, hKcore, hzero⟩ := hψ.2.2
  exact ⟨K, hK, hKcore, fun r hr θ =>
    r11b_directionalPartial_zero_outside hK.isClosed hzero d hr θ⟩

theorem r11b_radialTest_radialPartial {D : ReferenceData}
    {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) :
    RadialTest D (radialPartial ψ) :=
  r11b_radialTest_directionalPartial hψ (1, 0)

theorem r11b_radialTest_angularPartial {D : ReferenceData}
    {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) :
    RadialTest D (angularPartial ψ) :=
  r11b_radialTest_directionalPartial hψ (0, 1)

/-- The apparent quotient singularity lies in the flat zero region. -/
theorem r11b_continuous_flat_deriv_div {D : ReferenceData} (ha : 0 < D.a)
    {w : ℝ → ℝ} (hw : EndpointFlat D w) :
    Continuous (fun r : ℝ => deriv w r / r) := by
  have hdw : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw.1).2.continuous
  have hzero : ∀ r : ℝ, r < D.a → deriv w r = 0 := by
    intro r hr
    have heq : w =ᶠ[𝓝 r] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hr] with s hs
      exact hw.2 s (Or.inl hs.le)
    rw [heq.deriv_eq]
    exact deriv_const r 0
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : r = 0
  · subst r
    have heq : (fun s : ℝ => deriv w s / s) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds ha] with s hs
      rw [hzero s hs, zero_div]
    exact continuousAt_const.congr heq.symm
  · exact hdw.continuousAt.div continuousAt_id hr

theorem r11b_continuous_radialJacobi {D : ReferenceData} (ha : 0 < D.a)
    {w u : ℝ → ℝ} (hw : EndpointFlat D w) (hu : ContDiff ℝ ∞ u) (j : ℝ) :
    Continuous (radialJacobi j w u) := by
  have hdu : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hflux : ContDiff ℝ ∞ (fun r => w r * deriv u r) := hw.1.mul hdu
  have hflux' : Continuous (deriv (fun r => w r * deriv u r)) :=
    (contDiff_infty_iff_deriv.mp hflux).2.continuous
  simpa only [radialJacobi, mul_div_assoc] using
    hflux'.sub (((show Continuous (fun _ : ℝ => j) from continuous_const).mul (r11b_continuous_flat_deriv_div ha hw)).mul hu.continuous)

theorem r11b_continuous_referenceColumn {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    Continuous (referenceColumn D) := by
  have hflat : EndpointFlat D (fun r => D.w r * D.chi r) := by
    refine ⟨hgeom.2.2.1.1.mul hborder.1, fun r hr => ?_⟩
    change D.w r * D.chi r = 0
    rw [hgeom.2.2.1.2 r hr, zero_mul]
  exact r11b_continuous_radialJacobi hgeom.1 hflat hgeom.2.2.2.1.1 4

theorem r11b_continuous_radialPDE_test {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (fun x : PolarPoint => radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2) := by
  have hwr : Continuous (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2.continuous
  have hr : ContDiff ℝ ∞ (radialPartial ψ) :=
    r11b_contDiff_directionalPartial hψ (1, 0)
  have hrr : ContDiff ℝ ∞ (radialPartial (radialPartial ψ)) :=
    r11b_contDiff_directionalPartial hr (1, 0)
  have hθ : ContDiff ℝ ∞ (angularPartial ψ) :=
    r11b_contDiff_directionalPartial hψ (0, 1)
  have hθθ : ContDiff ℝ ∞ (angularPartial (angularPartial ψ)) :=
    r11b_contDiff_directionalPartial hθ (0, 1)
  have heq : (fun x : PolarPoint => radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2) =
      (fun x => deriv D.w x.1 * radialPartial ψ x +
        D.w x.1 * radialPartial (radialPartial ψ) x +
        deriv D.w x.1 / x.1 * angularPartial (angularPartial ψ) x) := by
    funext x
    exact radialPDE_eq_polar_jets (hgeom.2.2.1.1.differentiable (by simp) x.1) hψ
  rw [heq]
  exact (((hwr.comp continuous_fst).mul hr.continuous).add
    ((hgeom.2.2.1.1.continuous.comp continuous_fst).mul hrr.continuous)).add
      (((r11b_continuous_flat_deriv_div hgeom.1 hgeom.2.2.1).comp continuous_fst).mul
        hθθ.continuous)

/-- Applying the differential expression does not enlarge radial support. -/
theorem r11b_radialPDE_test_zero_outside {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0) {r : ℝ} (hr : r ∉ K) (θ : ℝ) :
    radialPDE D.w (fun s φ => ψ (s, φ)) r θ = 0 := by
  have hzR : ∀ s ∉ K, ∀ φ, radialPartial ψ (s, φ) = 0 :=
    fun s hs φ => r11b_directionalPartial_zero_outside hK hzero (1, 0) hs φ
  have hzA : ∀ s ∉ K, ∀ φ, angularPartial ψ (s, φ) = 0 :=
    fun s hs φ => r11b_directionalPartial_zero_outside hK hzero (0, 1) hs φ
  rw [radialPDE_eq_polar_jets (x := (r, θ))
    (hgeom.2.2.1.1.differentiable (by simp) r) hψ,
    hzR r hr θ,
    show radialPartial (radialPartial ψ) (r, θ) = 0 from
      r11b_directionalPartial_zero_outside hK hzR (1, 0) hr θ,
    show angularPartial (angularPartial ψ) (r, θ) = 0 from
      r11b_directionalPartial_zero_outside hK hzA (0, 1) hr θ]
  simp only [mul_zero, add_zero]

theorem r11b_radialPDE_test_pairing_integrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} {U : RadialUnknown} (hU : OutputMember D γ M U)
    {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) :
    Integrable (fun x : PolarPoint =>
      U.1 x * radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2) (radialPhysicalMeasure D) := by
  obtain ⟨C, hgeom, hrest⟩ := hD
  apply r11b_output_pairing_integrable ⟨C, hgeom, hrest⟩ hborder hU
    (r11b_continuous_radialPDE_test hgeom hψ.1)
  obtain ⟨K, hK, hKcore, hzero⟩ := hψ.2.2
  exact ⟨K, hK, hKcore, fun r hr θ =>
    r11b_radialPDE_test_zero_outside hgeom hψ.1 hK.isClosed hzero hr θ⟩

end ContinuousFlexibility.Radial
