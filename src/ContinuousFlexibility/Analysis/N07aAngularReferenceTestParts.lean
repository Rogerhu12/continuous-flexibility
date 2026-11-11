import ContinuousFlexibility.Analysis.N07aAngularReferenceDecomposition
import ContinuousFlexibility.Radial.R11bRadialTests

/-!
# The actual radial and angular pieces of an original reference test
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped Topology ContDiff

def n07aReferenceTestNormal (D : ReferenceData) (φ : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  deriv D.w p.1 * radialPartial φ p + D.w p.1 * radialPartial (radialPartial φ) p

def n07aReferenceTestAngular (D : ReferenceData) (φ : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  deriv D.w p.1 / p.1 * angularPartial (angularPartial φ) p

theorem n07a_referenceTestNormal_slice {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hw : Differentiable ℝ D.w) (hφ : ContDiff ℝ ∞ φ) (r θ : ℝ) :
    n07aReferenceTestNormal D φ (r, θ) =
      deriv (fun s => D.w s * deriv (fun t => φ (t, θ)) s) r := by
  have he : deriv (fun t => φ (t, θ)) = (fun t => radialPartial φ (t, θ)) :=
    funext fun t => (hasDerivAt_radialSlice (hφ.differentiable (by simp) (t, θ))).deriv
  rw [he]
  exact ((hw r).hasDerivAt.mul (hasDerivAt_radialSlice
    ((r11b_contDiff_directionalPartial hφ (1, 0)).differentiable (by simp) (r, θ)))).deriv.symm

theorem n07a_referenceTest_parts {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hw : Differentiable ℝ D.w) (hφ : ContDiff ℝ ∞ φ) (p : PolarPoint) :
    radialPDE D.w (fun r θ => φ (r, θ)) p.1 p.2 =
      n07aReferenceTestNormal D φ p + n07aReferenceTestAngular D φ p :=
  radialPDE_eq_polar_jets (hw p.1) hφ

theorem n07a_referenceTestParts_continuous_support {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    Continuous (n07aReferenceTestNormal D φ) ∧
    Continuous (n07aReferenceTestAngular D φ) ∧
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      ∀ r ∉ J, ∀ θ, n07aReferenceTestNormal D φ (r, θ) = 0 ∧
        n07aReferenceTestAngular D φ (r, θ) = 0 := by
  have hr := r11b_contDiff_directionalPartial hφ.1 (1, 0)
  have hrr := r11b_contDiff_directionalPartial hr (1, 0)
  have hθ := r11b_contDiff_directionalPartial hφ.1 (0, 1)
  have hθθ := r11b_contDiff_directionalPartial hθ (0, 1)
  have hN : Continuous (n07aReferenceTestNormal D φ) :=
    ((((contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2.continuous).comp continuous_fst).mul
      hr.continuous).add
      ((hgeom.2.2.1.1.continuous.comp continuous_fst).mul hrr.continuous)
  have hA : Continuous (n07aReferenceTestAngular D φ) :=
    ((r11b_continuous_flat_deriv_div hgeom.1 hgeom.2.2.1).comp continuous_fst).mul
      hθθ.continuous
  obtain ⟨J, hJ, hJD, hzero⟩ := hφ.2.2
  refine ⟨hN, hA, J, hJ, hJD, ?_⟩
  intro r hrJ θ
  have hzR : ∀ s ∉ J, ∀ t, radialPartial φ (s, t) = 0 :=
    fun s hs t => r11b_directionalPartial_zero_outside hJ.isClosed hzero (1, 0) hs t
  have hzA : ∀ s ∉ J, ∀ t, angularPartial φ (s, t) = 0 :=
    fun s hs t => r11b_directionalPartial_zero_outside hJ.isClosed hzero (0, 1) hs t
  simp only [n07aReferenceTestNormal, n07aReferenceTestAngular, hzR r hrJ θ,
    show radialPartial (radialPartial φ) (r, θ) = 0 from
      r11b_directionalPartial_zero_outside hJ.isClosed hzR (1, 0) hrJ θ,
    show angularPartial (angularPartial φ) (r, θ) = 0 from
      r11b_directionalPartial_zero_outside hJ.isClosed hzA (0, 1) hrJ θ,
    mul_zero, add_zero, and_self]

theorem n07a_physical_integrable_mul_continuous {D : ReferenceData}
    {f φ : PolarPoint → ℝ} (hf : Integrable f (radialPhysicalMeasure D))
    (hφ : Continuous φ) : Integrable (fun p => f p * φ p) (radialPhysicalMeasure D) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (hφ.norm.continuousOn (s := Icc D.a D.b ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
  apply hf.mul_bdd hφ.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact hB ⟨p, ⟨Ioo_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩, rfl⟩

theorem n07a_reference_angular_green_on_piece {D : ReferenceData}
    {S : PhysicalSpacesData} {K : CanonicalData S} {v φ : PolarPoint → ℝ}
    {m : ℕ} (hv : ContDiffOn ℝ ∞ v (physicalPieceOpen S K m))
    (hvp : Function.Periodic v (0, Real.pi)) (hφ : RadialTest D φ)
    {r : ℝ} (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, v (r, θ) * n07aReferenceTestAngular D φ (r, θ)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        (n07aReferenceInteriorDifferential D K v (r, θ) -
          n07aReferenceNormalSource D K v (r, θ)) * φ (r, θ) := by
  have hat (θ : ℝ) : ContDiffAt ℝ ∞ v (r, θ) :=
    hv.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)
  have hvθ : ContDiff ℝ ∞ (fun θ => v (r, θ)) := by
    rw [contDiff_iff_contDiffAt]
    exact fun θ => (hat θ).comp θ (contDiffAt_const.prodMk contDiffAt_id)
  have hvpθ : Function.Periodic (fun θ => v (r, θ)) (2 * Real.pi) := by
    intro θ
    have h₁ := hvp (r, θ)
    have h₂ := hvp (r, θ + Real.pi)
    simp only [Prod.mk_add_mk, add_zero] at h₁ h₂
    convert h₂.trans h₁ using 1 <;> congr 1 <;> ring
  have hφpθ : Function.Periodic (fun θ => φ (r, θ)) (2 * Real.pi) := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (r, θ)
  have hφθ : ContDiff ℝ ∞ (fun θ => φ (r, θ)) := by
    simpa only [Function.comp_def, id_eq] using
      hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have hgreen := reference_integral_periodic_mul_second_deriv hvθ hφθ hvpθ hφpθ
  have hleft (θ : ℝ) : v (r, θ) * n07aReferenceTestAngular D φ (r, θ) =
      (deriv D.w r / r) * (v (r, θ) * deriv (deriv (fun t => φ (r, t))) θ) := by
    rw [n07a_angularSlice_second_eq (p := (r, θ)) hφ.1.contDiffAt]
    dsimp only [n07aReferenceTestAngular]
    ring
  have hright (θ : ℝ) :
      (n07aReferenceInteriorDifferential D K v (r, θ) -
        n07aReferenceNormalSource D K v (r, θ)) * φ (r, θ) =
      (deriv D.w r / r) * (deriv (deriv (fun t => v (r, t))) θ * φ (r, θ)) := by
    have hp : (r, θ) ∈ n07aReferencePieceInterior K := mem_iUnion.mpr ⟨m, ⟨hr, mem_univ _⟩⟩
    rw [n07aReferenceInteriorDifferential, n07aReferenceNormalSource,
      indicator_of_mem hp, indicator_of_mem hp, n07a_angularSlice_second_eq (hat θ)]
    dsimp only [n07aReferenceDifferential]
    ring
  simp_rw [hleft, hright]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hgreen]

end ContinuousFlexibility.Analysis
