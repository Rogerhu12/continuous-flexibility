module

public import ContinuousFlexibility.Analysis.N06PositiveCurrentTestLp
public import ContinuousFlexibility.Analysis.N06CubicDifferential
public import ContinuousFlexibility.Analysis.N06ReferencePhysicalCoefficients
public import ContinuousFlexibility.Analysis.N06FiniteReferenceColumns

/-!
# The actual corrected left-tail column

The derivative of the original physical cutoff has a fixed compact
support in the positive-type region. N03 leaves the actual coefficient
germs unchanged there. Off that support both fluxes vanish on a
neighborhood, regardless of coefficient regularity. Thus the genuine
corrected left column equals its original-coefficient expression on the
whole plane, is smooth, and has the original common compact support.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

theorem n06_divergence_radial_cutoff_flux (A : SymmetricCoefficients)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (p : PolarPoint) :
    divergenceOperator A (n06ReferenceLeftField χ) p =
      radialPartial (fun q => A.a q * deriv χ q.1) p +
        angularPartial (fun q => A.b q * deriv χ q.1) p := by
  have hr : radialPartial (n06ReferenceLeftField χ) =
      fun q => deriv χ q.1 :=
    funext (fun q => radialPartial_radialHeightField (hχ.differentiable (by simp) q.1))
  have ht : angularPartial (n06ReferenceLeftField χ) = fun _ => (0 : ℝ) :=
    funext (fun q => angularPartial_radialHeightField (hχ.differentiable (by simp) q.1))
  simp only [divergenceOperator, hr, ht, mul_zero, add_zero]

theorem n06_cutoff_flux_zero_germ (a : PolarPoint → ℝ)
    {χ : ℝ → ℝ} {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → deriv χ r = 0)
    {p : PolarPoint} (hp : p.1 ∉ J) :
    (fun q => a q * deriv χ q.1) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
  filter_upwards [(continuous_fst.tendsto p).eventually
    (hJ.isOpen_compl.mem_nhds hp)] with q hq
  simp only [hzero q.1 hq, mul_zero]

theorem n06_divergence_radial_cutoff_zero (A : SymmetricCoefficients)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → deriv χ r = 0)
    {p : PolarPoint} (hp : p.1 ∉ J) :
    divergenceOperator A (n06ReferenceLeftField χ) p = 0 := by
  have hrad : radialPartial (fun q => A.a q * deriv χ q.1) p = 0 := by
    simpa only [radialPartial, fderiv_const_apply, zero_apply] using
      congrArg (fun F : PolarPoint →L[ℝ] ℝ => F (1, 0))
        (n06_cutoff_flux_zero_germ A.a hJ hzero hp).fderiv_eq
  have hang : angularPartial (fun q => A.b q * deriv χ q.1) p = 0 := by
    simpa only [angularPartial, fderiv_const_apply, zero_apply] using
      congrArg (fun F : PolarPoint →L[ℝ] ℝ => F (0, 1))
        (n06_cutoff_flux_zero_germ A.b hJ hzero hp).fderiv_eq
  exact (n06_divergence_radial_cutoff_flux A hχ p).trans
    (by rw [hrad, hang, zero_add])

theorem n06_cutoff_flux_contDiff (a : PolarPoint → ℝ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → deriv χ r = 0)
    (ha : ∀ p : PolarPoint, p.1 ∈ J → ContDiffAt ℝ ∞ a p) :
    ContDiff ℝ ∞ (fun p => a p * deriv χ p.1) := by
  have hχ' : ContDiff ℝ ∞ (fun p : PolarPoint => deriv χ p.1) :=
    (contDiff_infty_iff_deriv.mp hχ).2.comp contDiff_fst
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ J
  · exact (ha p hp).mul hχ'.contDiffAt
  · exact contDiffAt_const.congr_of_eventuallyEq
      (n06_cutoff_flux_zero_germ a hJ hzero hp)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

def n06CurrentLeftColumn (S : PhysicalSpacesData) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  divergenceOperator (L.coefficients z) (n06ReferenceLeftField S.chiLeft)

/-- The cutoff is S.chiLeft throughout. The correction vanishes on its
positive support, while its derivative vanishes off that support. -/
theorem n06_currentLeftColumn_eq_original
    (hS : IsPhysicalSpaces D T S) (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (p : PolarPoint) :
    n06CurrentLeftColumn S L z p =
      divergenceOperator (originalCoefficients D S C z)
        (n06ReferenceLeftField S.chiLeft) p := by
  have hχ : CutoffConditions D S.chiLeft := hS.2.2.1
  obtain ⟨J, hJ, hJD, hpos, hzero⟩ := hχ.2.2
  change divergenceOperator (L.coefficients z) (n06ReferenceLeftField S.chiLeft) p = _
  by_cases hp : p.1 ∈ J
  · have hbc := h03.2.1 z hz hs p ⟨hJD hp, mem_univ _⟩ (hpos p.1 hp)
    exact n06_divergenceOperator_congr_germ (n06ReferenceLeftField S.chiLeft)
      (Filter.Eventually.of_forall (h03.1 z hz hs)) hbc.1 hbc.2
  · exact (n06_divergence_radial_cutoff_zero (L.coefficients z) hχ.1 hJ.isClosed hzero hp).trans
      (n06_divergence_radial_cutoff_zero (originalCoefficients D S C z)
        hχ.1 hJ.isClosed hzero hp).symm

/-- All allowed current left columns have one genuine compact physical
support, independent of the state. -/
theorem n06_currentLeftColumns_commonSupport (hS : IsPhysicalSpaces D T S) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      (∀ r ∈ J, 0 < deriv D.w r) ∧
      ∀ z : AnnularState S × ℝ, ∀ r, r ∉ J → ∀ θ,
        n06CurrentLeftColumn S L z (r, θ) = 0 := by
  have hχ : CutoffConditions D S.chiLeft := hS.2.2.1
  obtain ⟨J, hJ, hJD, hpos, hzero⟩ := hχ.2.2
  refine ⟨J, hJ, hJD, hpos, ?_⟩
  intro z r hr θ
  exact n06_divergence_radial_cutoff_zero (L.coefficients z) hχ.1 hJ.isClosed hzero
    (p := (r, θ)) hr

theorem n06_currentLeftColumn_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) : ContDiff ℝ ∞ (n06CurrentLeftColumn S L z) := by
  have hχ : CutoffConditions D S.chiLeft := hS.2.2.1
  obtain ⟨J, hJ, hJD, hpos, hzero⟩ := hχ.2.2
  have hreg (p : PolarPoint) (hp : p.1 ∈ J) :=
    n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03 hz hs
      (p := p) ⟨hJD hp, mem_univ _⟩ (hpos p.1 hp).le
  have ha : ContDiff ℝ ∞ (fun p => (L.coefficients z).a p * deriv S.chiLeft p.1) :=
    n06_cutoff_flux_contDiff _ hχ.1 hJ.isClosed hzero (fun p hp => (hreg p hp).1)
  have hb : ContDiff ℝ ∞ (fun p => (L.coefficients z).b p * deriv S.chiLeft p.1) :=
    n06_cutoff_flux_contDiff _ hχ.1 hJ.isClosed hzero (fun p hp => (hreg p hp).2.1)
  have he : n06CurrentLeftColumn S L z = fun p =>
      radialPartial (fun q => (L.coefficients z).a q * deriv S.chiLeft q.1) p +
      angularPartial (fun q => (L.coefficients z).b q * deriv S.chiLeft q.1) p :=
    funext (n06_divergence_radial_cutoff_flux (L.coefficients z) hχ.1)
  rw [he]
  exact (contDiff_cylinder_radialPartial ha).add (contDiff_cylinder_angularPartial hb)

/-- The reference value is exactly the existing physical left forcing.
Only N01 and N03 are needed for this particular compactly supported
column; no separate reference test identity is assumed. -/
theorem n06_currentLeftColumn_reference
    (hS : IsPhysicalSpaces D T S) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) (p : PolarPoint) :
    n06CurrentLeftColumn S L (C.referenceState, 0) p =
      n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) p := by
  have hw : ContDiff ℝ ∞ D.w := h01.1.1.choose_spec.1.2.2.1.1
  have hχ : ContDiff ℝ ∞ S.chiLeft := hS.2.2.1.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have ha : (originalCoefficients D S C (C.referenceState, 0)).a =
      fun q => D.w q.1 :=
    funext (fun q => (n06_originalCoefficients_reference hw h01.2.2.1 q).1)
  have hb : (originalCoefficients D S C (C.referenceState, 0)).b =
      fun _ => (0 : ℝ) :=
    funext (fun q => (n06_originalCoefficients_reference hw h01.2.2.1 q).2.1)
  rw [n06_currentLeftColumn_eq_original hS h03 href hs p,
    n06_divergence_radial_cutoff_flux _ hχ p, ha, hb]
  simp only [zero_mul, angularPartial_const, add_zero]
  have hflux : DifferentiableAt ℝ (fun r => D.w r * deriv S.chiLeft r) p.1 :=
    (hw.mul (contDiff_infty_iff_deriv.mp hχ).2).differentiable (by simp) p.1
  exact (radialPartial_radialHeightField hflux).trans
    (n06_referenceLeftColumn_formula D S.chiLeft p).symm

end ContinuousFlexibility.Statements
