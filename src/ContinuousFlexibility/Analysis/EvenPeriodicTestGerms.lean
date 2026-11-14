module

public import ContinuousFlexibility.Analysis.CompactEvenHeightTests
public import ContinuousFlexibility.Analysis.PlanarInverseRegularity
public import ContinuousFlexibility.Analysis.ReverseCoordinateOperator
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Genuine even periodic test germs away from the reflection axes

The map `(r, θ) ↦ (r, cos (2θ))` is a true smooth local coordinate
system away from the axes. A smooth function in these coordinates is
automatically even and π-periodic. A radial bump gives compact physical
support. The resulting height test agrees on a neighborhood with the
prescribed smooth function; matching a finite list of jets is not assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A genuine local diffeomorphism represents every smooth germ by the
pullback of a global smooth function. The inverse is made smooth on an
actual open set by restricting to the nonzero-Jacobian locus. -/
theorem exists_global_contDiff_pullback_germ
    {F : PolarPoint → PolarPoint} (hF : ContDiff ℝ ∞ F)
    {p : PolarPoint} (hJ : planeJacobian F p ≠ 0)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∃ g : PolarPoint → ℝ, ContDiff ℝ ∞ g ∧
      (fun q => g (F q)) =ᶠ[𝓝 p] u := by
  obtain ⟨e, he, hpe, _⟩ :=
    exists_smooth_localInverse_of_planeJacobian_ne_zero hF.contDiffAt hJ
  let U : Set PolarPoint := {q | planeJacobian F q ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (continuous_planeJacobian hF) continuous_const
  let e' : OpenPartialHomeomorph PolarPoint PolarPoint := e.restrOpen U hU
  have he' : (e' : PolarPoint → PolarPoint) = F :=
    (OpenPartialHomeomorph.coe_restrOpen (e := e) hU).trans he
  have hsource : e'.source = e.source ∩ U := e.restrOpen_source U hU
  have hp' : p ∈ e'.source := by rw [hsource]; exact ⟨hpe, hJ⟩
  have htarget : F p ∈ e'.target := by rw [← he']; exact e'.map_source hp'
  have hJF : ∀ q ∈ e'.source, planeJacobian F q ≠ 0 := by
    intro q hq
    exact (hsource ▸ hq).2
  have hInj : InjOn F e'.source := by rw [← he']; exact e'.injOn
  have hRight : RightInvOn e'.symm F e'.target := by
    rw [← he']
    exact e'.rightInvOn
  have hInv : ContDiffOn ℝ ∞ e'.symm e'.target :=
    contDiffOn_planar_rightInverse_of_injOn e'.open_source e'.open_target
      hF.contDiffOn hJF hInj e'.symm.mapsTo hRight
  obtain ⟨g, hg, hgerm⟩ := exists_global_contDiff_germ_of_open e'.open_target
    (hu.comp_contDiffOn hInv) htarget
  refine ⟨g, hg, ?_⟩
  filter_upwards [hF.continuous.continuousAt.eventually hgerm,
    e'.open_source.mem_nhds hp'] with q hq hqs
  calc
    g (F q) = u (e'.symm (F q)) := hq
    _ = u q := by rw [← he', e'.left_inv hqs]

def evenCosineChart (p : PolarPoint) : PolarPoint :=
  (p.1, Real.cos (2 * p.2))

theorem contDiff_evenCosineChart : ContDiff ℝ ∞ evenCosineChart :=
  contDiff_fst.prodMk (contDiff_const.mul contDiff_snd).cos

theorem planeJacobian_evenCosineChart (p : PolarPoint) :
    planeJacobian evenCosineChart p = -2 * Real.sin (2 * p.2) := by
  have hfst : HasFDerivAt (fun q : PolarPoint => q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun q : PolarPoint => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hDF := hfst.prodMk ((hsnd.const_mul (2 : ℝ)).cos)
  change HasFDerivAt evenCosineChart _ p at hDF
  unfold planeJacobian
  rw [hDF.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul]
  ring

theorem evenCosineChart_even (r θ : ℝ) :
    evenCosineChart (r, -θ) = evenCosineChart (r, θ) := by
  simp only [evenCosineChart, mul_neg, Real.cos_neg]

theorem evenCosineChart_periodic :
    Function.Periodic evenCosineChart (0, Real.pi) := by
  intro p
  simp only [evenCosineChart, Prod.fst_add, Prod.snd_add, add_zero]
  rw [mul_add, Real.cos_add_two_pi]

/-- Away from an angular reflection axis, every genuine smooth germ has
an even periodic representative with compact radial support. -/
theorem exists_compact_even_periodic_germ_of_nonaxis
    {D : ReferenceData} {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hsin : Real.sin (2 * p.2) ≠ 0)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∃ f : PolarPoint → ℝ, ContDiff ℝ ∞ f ∧
      (∀ r θ, f (r, -θ) = f (r, θ)) ∧
      Function.Periodic f (0, Real.pi) ∧
      HasCompactRadialSupport D f ∧ f =ᶠ[𝓝 p] u := by
  have hJ : planeJacobian evenCosineChart p ≠ 0 := by
    rw [planeJacobian_evenCosineChart]
    exact mul_ne_zero (by norm_num) hsin
  obtain ⟨g, hg, hgerm⟩ :=
    exists_global_contDiff_pullback_germ contDiff_evenCosineChart hJ hu
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds hp.1)
  let χ : ContDiffBump p.1 :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hsupport : tsupport (χ : ℝ → ℝ) ⊆ Ioo D.a D.b := by
    rw [χ.tsupport_eq]
    intro r hr
    apply hball
    apply Metric.mem_ball.mpr
    have hr' : dist r p.1 ≤ ε / 2 := Metric.mem_closedBall.mp hr
    linarith
  let f : PolarPoint → ℝ := fun q => χ q.1 * g (evenCosineChart q)
  have hf : ContDiff ℝ ∞ f :=
    (χ.contDiff.comp contDiff_fst).mul (hg.comp contDiff_evenCosineChart)
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · intro r θ
    simp only [f, evenCosineChart_even]
  · intro q
    simp only [f, Prod.fst_add, add_zero, evenCosineChart_periodic q]
  · refine ⟨tsupport (χ : ℝ → ℝ), χ.hasCompactSupport, hsupport, ?_⟩
    intro r hr θ
    have hz : χ r = 0 := image_eq_zero_of_notMem_tsupport hr
    simp only [f, hz, zero_mul]
  · have hχ : ∀ᶠ q : PolarPoint in 𝓝 p, χ q.1 = 1 :=
      continuous_fst.continuousAt.eventually χ.eventuallyEq_one
    filter_upwards [hχ, hgerm] with q hq hgu
    simpa only [f, hq, one_mul] using hgu

/-- The local representative is a genuine HeightPair field, so the N03
operator identity applies to it without any additional test-space axiom. -/
theorem exists_heightPair_germ_of_nonaxis
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hsin : Real.sin (2 * p.2) ≠ 0)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∃ η : HeightPair S, η.2 = 0 ∧ heightPairField S η =ᶠ[𝓝 p] u := by
  obtain ⟨f, hf, heven, hperiod, hsupport, hgerm⟩ :=
    exists_compact_even_periodic_germ_of_nonaxis hp hsin hu
  obtain ⟨η, hη, hfield⟩ := exists_heightPair_of_compact_even_periodic
    hT hS hf.contDiffOn heven hperiod hsupport
  refine ⟨η, hη, ?_⟩
  rw [hfield]
  exact hgerm

end ContinuousFlexibility.Analysis
