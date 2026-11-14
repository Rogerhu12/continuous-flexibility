module

public import ContinuousFlexibility.Analysis.N06CutoffCorrectionConservation
public import ContinuousFlexibility.Analysis.N06FiniteCurrentBoundaryGluing
public import ContinuousFlexibility.Analysis.N06CurrentPhysicalTests
public import ContinuousFlexibility.Analysis.SpacesSources

/-!
# The actual left column paired with compact even half-period tests

Green symmetry for the original coefficients is applied on a compact
interior window containing the true test support. There is no regularity
assumption at the flat annular ends. N03's weighted correction conservation
then replaces the original operator by the corrected one. All functions
are the original physical fields and all integrals use the source mean.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

theorem n06_test_zero_germ_of_radial_support
    {φ : PolarPoint → ℝ} {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0)
    {p : PolarPoint} (hp : p.1 ∉ J) : φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ) := by
  filter_upwards [(continuous_fst.tendsto p).eventually
    (hJ.isOpen_compl.mem_nhds hp)] with q hq
  exact hzero q.1 hq q.2

/-- Local annular operator smoothness extends across the complement of
the actual compact test support by its genuine zero germs. -/
theorem n06_test_divergence_contDiff_of_annular
    {D : ReferenceData} (A : SymmetricCoefficients) {φ : PolarPoint → ℝ}
    (hsupport : HasCompactRadialSupport D φ)
    (hlocal : ∀ p ∈ annularOpen D, ContDiffAt ℝ ∞ (divergenceOperator A φ) p) :
    ContDiff ℝ ∞ (divergenceOperator A φ) := by
  obtain ⟨J, hJ, hJD, hzero⟩ := hsupport
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ annularOpen D
  · exact hlocal p hp
  · have hpJ : p.1 ∉ J := fun h => hp ⟨hJD h, mem_univ _⟩
    exact contDiffAt_const.congr_of_eventuallyEq
      (n06_divergenceOperator_eventually_zero A
        (n06_test_zero_germ_of_radial_support hJ.isClosed hzero hpJ))

private theorem greenNormalFlux_zero_of_test_germ
    (A B χ : PolarPoint → ℝ) {φ : PolarPoint → ℝ} {p : PolarPoint}
    (hφ : φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ)) :
    greenNormalFlux A B χ φ p = 0 := by
  have hd : fderiv ℝ φ p = 0 := by
    have he := hφ.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ φ p = fderiv ℝ (fun _ : PolarPoint => (0 : ℝ)) p at he
    simpa only [fderiv_const_apply] using he
  simp only [greenNormalFlux, symmetricNormalFlux, hφ.eq_of_nhds,
    radialPartial, angularPartial, hd, zero_apply, Pi.zero_apply,
    mul_zero, zero_mul, add_zero, sub_zero]

/-- The original Green calculation only needs coefficient regularity
inside the annulus. Compact test support chooses the interior rectangle. -/
theorem n06_compact_radial_cutoff_green
    {D : ReferenceData} (hab : D.a < D.b) (A : SymmetricCoefficients)
    (hreg : ∀ p ∈ annularOpen D,
      ContDiffAt ℝ ∞ A.a p ∧ ContDiffAt ℝ ∞ A.b p ∧ ContDiffAt ℝ ∞ A.c p)
    (hb : Function.Periodic A.b (0, Real.pi))
    (hc : Function.Periodic A.c (0, Real.pi))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hp : Function.Periodic φ (0, Real.pi))
    (hsupport : HasCompactRadialSupport D φ) :
    physicalSourceIntegral D (fun p => χ p.1 * divergenceOperator A φ p -
      φ p * divergenceOperator A (fun q => χ q.1) p) = 0 := by
  obtain ⟨J, hJ, hJD, hzero⟩ := hsupport
  obtain ⟨l, r, hlr, hJlr, hlrD⟩ := n06_compact_openInterval_window hab hJ hJD
  let g : ℝ → ℝ := fun t => ∫ θ in (0 : ℝ)..Real.pi,
    χ t * divergenceOperator A φ (t, θ) - φ (t, θ) *
      divergenceOperator A (fun q => χ q.1) (t, θ)
  have hg : Function.support g ⊆ J := by
    intro t ht
    by_contra htJ
    have hL := n06_divergenceOperator_zero_off_radial_support A hJ.isClosed hzero htJ
    have he : g t = 0 := by
      simp only [g, hzero t htJ, hL, mul_zero, zero_mul, sub_self,
        intervalIntegral.integral_zero]
    exact ht he
  have hends (t : ℝ) (ht : t ∉ J) (θ : ℝ) :
      greenNormalFlux A.a A.b (fun q => χ q.1) φ (t, θ) = 0 :=
    greenNormalFlux_zero_of_test_germ A.a A.b _
      (n06_test_zero_germ_of_radial_support hJ.isClosed hzero ht)
  have hlocal (p : PolarPoint) (hp : p ∈ uIcc l r ×ˢ uIcc 0 Real.pi) :=
    hreg p ⟨hlrD (by simpa only [uIcc_of_le hlr.le] using hp.1), mem_univ _⟩
  have hgreen := integral_symmetric_green_eq_zero_of_periodic
    (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2.1)
    (fun p hp => (hlocal p hp).2.2)
    (fun _ _ => (hχ.comp contDiff_fst).contDiffAt) (fun _ _ => hφ.contDiffAt)
    hb hc (fun p => by simp only [Function.comp_def, Prod.fst_add, add_zero]) hp
    (fun θ _ => hends l (fun ht => (lt_irrefl l) (hJlr ht).1) θ)
    (fun θ _ => hends r (fun ht => (lt_irrefl r) (hJlr ht).2) θ)
  have hgreen' : (∫ t in l..r, g t) = 0 := hgreen
  have hDsupport : Function.support g ⊆ Ioc D.a D.b :=
    hg.trans (hJD.trans Ioo_subset_Ioc_self)
  have hWsupport : Function.support g ⊆ Ioc l r :=
    hg.trans (hJlr.trans Ioo_subset_Ioc_self)
  unfold physicalSourceIntegral angularMean
  rw [intervalIntegral.integral_const_mul]
  change (1 / Real.pi) * (∫ t in D.a..D.b, g t) = 0
  rw [intervalIntegral.integral_eq_integral_of_support_subset hDsupport,
    ← intervalIntegral.integral_eq_integral_of_support_subset hWsupport, hgreen', mul_zero]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

private theorem n06_sourceIntegral_sub (D : ReferenceData) {f g : PolarPoint → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    physicalSourceIntegral D (fun p => f p - g p) =
      physicalSourceIntegral D f - physicalSourceIntegral D g := by
  simpa only [physicalSourceIntegral, angularMean, Pi.add_apply, Pi.neg_apply,
    intervalIntegral.integral_neg, mul_neg, sub_eq_add_neg] using
    spaces_physicalSourceIntegral_add D hf hg.neg

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

/-- This is the literal current left-column pairing for the genuine
compact even half-period tests. N03 supplies the correction conservation,
and all splitting is justified by actual global smoothness of the tested
operator values, not of the bare corrected coefficients. -/
theorem n06_currentLeftColumn_half_pairing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (heven : ∀ r θ, φ (r, -θ) = φ (r, θ))
    (hperiod : Function.Periodic φ (0, Real.pi))
    (hsupport : HasCompactRadialSupport D φ) :
    physicalSourceIntegral D (fun p => S.chiLeft p.1 *
      divergenceOperator (L.coefficients z) φ p) =
      physicalSourceIntegral D (fun p => n06CurrentLeftColumn S L z p * φ p) := by
  have hreg (p : PolarPoint) (hp : p ∈ annularOpen D) :=
    n06_originalCoefficients_contDiffAt hT hS h01 hz hs hp
  have hLo : ContDiff ℝ ∞ (divergenceOperator (originalCoefficients D S C z) φ) :=
    n06_test_divergence_contDiff_of_annular _ hsupport (fun p hp =>
      n06_contDiffAt_divergenceOperator (hreg p hp).1 (hreg p hp).2.1
        (hreg p hp).2.2 hφ.contDiffAt)
  obtain ⟨η, hη⟩ := n05_exists_heightPair_of_compact_test hT hS hφ heven hperiod hsupport
  have hLc : ContDiff ℝ ∞ (divergenceOperator (L.coefficients z) φ) := by
    apply n06_test_divergence_contDiff_of_annular _ hsupport
    intro p hp
    have hh := n06_correctedDivergence_heightPair_contDiffAt hT hS h01 h03 hz hs η hp
    rwa [hη] at hh
  have hχ : ContDiff ℝ ∞ (fun p : PolarPoint => S.chiLeft p.1) :=
    hS.2.2.1.1.comp contDiff_fst
  have hc : ContDiff ℝ ∞ (n06CurrentLeftColumn S L z) :=
    n06_currentLeftColumn_contDiff hT hS h01 h03 hz hs
  have hconserve := n06_cutoff_correction_conservation hT hS h01 h03 hz hs
    hφ heven hperiod hsupport
  have he : (fun p => S.chiLeft p.1 *
      (divergenceOperator (originalCoefficients D S C z) φ p -
        divergenceOperator (L.coefficients z) φ p)) =
      fun p => (S.chiLeft p.1 * divergenceOperator (originalCoefficients D S C z) φ p) -
        (S.chiLeft p.1 * divergenceOperator (L.coefficients z) φ p) := by
    funext p
    ring
  rw [he, n06_sourceIntegral_sub D (hχ.mul hLo).continuous (hχ.mul hLc).continuous] at hconserve
  have hper := n06_originalCoefficients_periodic (C := C) hS z
  have hgreen := n06_compact_radial_cutoff_green h01.1.1.choose_spec.1.2.1
    (originalCoefficients D S C z) hreg hper.2.1 hper.2.2
    hS.2.2.1.1 hφ hperiod hsupport
  have hegreen : (fun p => S.chiLeft p.1 *
      divergenceOperator (originalCoefficients D S C z) φ p - φ p *
        divergenceOperator (originalCoefficients D S C z) (fun q => S.chiLeft q.1) p) =
      fun p => S.chiLeft p.1 * divergenceOperator (originalCoefficients D S C z) φ p -
        n06CurrentLeftColumn S L z p * φ p := by
    funext p
    rw [n06_currentLeftColumn_eq_original hS h03 hz hs p]
    congr 1
    exact mul_comm _ _
  rw [hegreen, n06_sourceIntegral_sub D (hχ.mul hLo).continuous (hc.mul hφ).continuous] at hgreen
  exact (sub_eq_zero.mp hconserve).symm.trans (sub_eq_zero.mp hgreen)

end ContinuousFlexibility.Statements
