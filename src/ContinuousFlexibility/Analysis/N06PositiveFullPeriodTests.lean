module

public import ContinuousFlexibility.Analysis.N06AveragedWeakTests
public import ContinuousFlexibility.Analysis.N06CubicDifferential
public import ContinuousFlexibility.Analysis.N06PositiveCurrentTestLp
public import ContinuousFlexibility.Analysis.N06CurrentOperatorPeriodicity

/-!
# Full-period test averaging on the actual positive pieces

On positive pieces N03 identifies the corrected coefficients with the
original coefficients on genuine neighborhoods. The original coefficients
have period pi and are smooth locally in the physical annulus. Those local
facts suffice to commute the actual operator with half-period averaging;
no global smooth extension of physical coefficients is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem average_fderiv_at {f : PolarPoint → ℝ} {p : PolarPoint}
    (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ f (p + (0, Real.pi))) (v : PolarPoint) :
    fderiv ℝ (n06_radialTestAverage f) p v =
      n06_radialTestAverage (fun q => fderiv ℝ f q v) p := by
  have hshift : DifferentiableAt ℝ (fun q : PolarPoint => f (q + (0, Real.pi))) p :=
    hg.comp p (differentiableAt_id.add_const (0, Real.pi))
  have he : n06_radialTestAverage f =
      fun q => (1 / 2 : ℝ) * (f q + f (q + (0, Real.pi))) := by
    funext q
    rw [n06_radialTestAverage_apply]
    ring
  have hsum : DifferentiableAt ℝ (fun q => f q + f (q + (0, Real.pi))) p := hf.add hshift
  rw [he, fderiv_const_mul hsum (1 / 2), fderiv_fun_add hf hshift, fderiv_comp_add_right]
  simp only [smul_apply, add_apply,
    smul_eq_mul, n06_radialTestAverage_apply]
  ring

/-- Only the two physical germs appearing in the average need regularity. -/
theorem n06_divergenceOperator_average_at
    {A : SymmetricCoefficients} {φ : PolarPoint → ℝ} {p : PolarPoint}
    (hpa : Function.Periodic A.a (0, Real.pi))
    (hpb : Function.Periodic A.b (0, Real.pi))
    (hpc : Function.Periodic A.c (0, Real.pi))
    (ha : DifferentiableAt ℝ A.a p) (hb : DifferentiableAt ℝ A.b p)
    (hc : DifferentiableAt ℝ A.c p)
    (ha' : DifferentiableAt ℝ A.a (p + (0, Real.pi)))
    (hb' : DifferentiableAt ℝ A.b (p + (0, Real.pi)))
    (hc' : DifferentiableAt ℝ A.c (p + (0, Real.pi)))
    (hφ : ContDiff ℝ ∞ φ) :
    divergenceOperator A (n06_radialTestAverage φ) p =
      n06_radialTestAverage (divergenceOperator A φ) p := by
  let fr : PolarPoint → ℝ := fun q => A.a q * radialPartial φ q + A.b q * angularPartial φ q
  let ft : PolarPoint → ℝ := fun q => A.b q * radialPartial φ q + A.c q * angularPartial φ q
  have hfr : (fun q => A.a q * radialPartial (n06_radialTestAverage φ) q +
      A.b q * angularPartial (n06_radialTestAverage φ) q) = n06_radialTestAverage fr := by
    funext q
    rw [n06_radialPartial_radialTestAverage hφ, n06_angularPartial_radialTestAverage hφ]
    simp only [n06_radialTestAverage_apply, fr, hpa q, hpb q]
    ring
  have hft : (fun q => A.b q * radialPartial (n06_radialTestAverage φ) q +
      A.c q * angularPartial (n06_radialTestAverage φ) q) = n06_radialTestAverage ft := by
    funext q
    rw [n06_radialPartial_radialTestAverage hφ, n06_angularPartial_radialTestAverage hφ]
    simp only [n06_radialTestAverage_apply, ft, hpb q, hpc q]
    ring
  have hr := (contDiff_cylinder_radialPartial hφ).differentiable (by simp)
  have ht := (contDiff_cylinder_angularPartial hφ).differentiable (by simp)
  have hfr₀ : DifferentiableAt ℝ fr p := (ha.mul (hr p)).add (hb.mul (ht p))
  have hft₀ : DifferentiableAt ℝ ft p := (hb.mul (hr p)).add (hc.mul (ht p))
  have hfr₁ : DifferentiableAt ℝ fr (p + (0, Real.pi)) :=
    (ha'.mul (hr _)).add (hb'.mul (ht _))
  have hft₁ : DifferentiableAt ℝ ft (p + (0, Real.pi)) :=
    (hb'.mul (hr _)).add (hc'.mul (ht _))
  change radialPartial _ p + angularPartial _ p = _
  rw [hfr, hft]
  change fderiv ℝ (n06_radialTestAverage fr) p (1, 0) +
    fderiv ℝ (n06_radialTestAverage ft) p (0, 1) = _
  rw [average_fderiv_at hfr₀ hfr₁, average_fderiv_at hft₀ hft₁]
  simp only [n06_radialTestAverage_apply, divergenceOperator, radialPartial, angularPartial, fr, ft]
  ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- N03's positive and turning-point germs identify the operator itself. -/
theorem n06_correctedDivergence_eq_original_of_nonneg
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hw : 0 ≤ deriv D.w p.1)
    (φ : PolarPoint → ℝ) :
    divergenceOperator (L.coefficients z) φ p =
      divergenceOperator (originalCoefficients D S C z) φ p := by
  have hbc : (L.coefficients z).b =ᶠ[𝓝 p] (originalCoefficients D S C z).b ∧
      (L.coefficients z).c =ᶠ[𝓝 p] (originalCoefficients D S C z).c := by
    rcases lt_or_eq_of_le hw with h | h
    · exact h03.2.1 z hz hs p hp h
    · exact h03.2.2.1 z hz hs p hp h.symm
  exact n06_divergenceOperator_congr_germ φ
    (Eventually.of_forall (h03.1 z hz hs)) hbc.1 hbc.2

/-- The actual physical operator commutes with averaging on every
positive point; the test may have only the full physical period. -/
theorem n06_positiveDivergence_average
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hw : 0 ≤ deriv D.w p.1)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    divergenceOperator (L.coefficients z) (n06_radialTestAverage φ) p =
      n06_radialTestAverage (divergenceOperator (L.coefficients z) φ) p := by
  have hp' : p + (0, Real.pi) ∈ annularOpen D :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  have hw' : 0 ≤ deriv D.w (p + (0, Real.pi)).1 := by
    simpa only [Prod.fst_add, add_zero] using hw
  have hreg := n06_originalCoefficients_contDiffAt hT hS h01 hz hs hp
  have hreg' := n06_originalCoefficients_contDiffAt hT hS h01 hz hs hp'
  have hper := n06_originalCoefficients_periodic (C := C) hS z
  have he := n06_divergenceOperator_average_at hper.1 hper.2.1 hper.2.2
    (hreg.1.differentiableAt (by simp)) (hreg.2.1.differentiableAt (by simp))
    (hreg.2.2.differentiableAt (by simp)) (hreg'.1.differentiableAt (by simp))
    (hreg'.2.1.differentiableAt (by simp)) (hreg'.2.2.differentiableAt (by simp)) hφ
  rw [n06_radialTestAverage_apply] at he ⊢
  rw [n06_correctedDivergence_eq_original_of_nonneg h03 hz hs hp hw,
    n06_correctedDivergence_eq_original_of_nonneg h03 hz hs hp hw,
    n06_correctedDivergence_eq_original_of_nonneg h03 hz hs hp' hw']
  exact he

/-- The full physical pairing therefore uses exactly the source of the
averaged test operator on every actual positive canonical piece. -/
theorem n06_positive_current_source_average
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p =
      canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p := by
  have hq := (h04.1.charts z hz hs m).2.1 hp
  have hqa : K.inverseChart z m p ∈ annularOpen D :=
    (h04.1.domains z hz hs m).2.2.1 hq
  have hw := ((h04.1.domains z hz hs m).2.2.2.2.2.2.1 _ hq hm).le
  dsimp only [canonicalSource]
  rw [n06_positiveDivergence_average hT hS h01 h03 hz hs hqa hw hφ]

end ContinuousFlexibility.Statements
