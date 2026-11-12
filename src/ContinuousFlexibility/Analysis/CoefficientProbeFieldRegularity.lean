import ContinuousFlexibility.Analysis.N03CoefficientProbeIdentity
import ContinuousFlexibility.Analysis.MaterialHeightRegularity
import ContinuousFlexibility.Analysis.LocalMixedProductBounds
import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport

/-!
# Actual smooth probe fields and their two angular centers

Decoded source errors are genuinely smooth on the whole physical plane.
Their two probe numerators retain evenness, angular periodicity and zero
extension outside the annulus. A fixed finite correction removes the two
axis values everywhere while leaving the entire germ unchanged wherever
those values already vanish. Evenness and periodicity give the true first
angular zero jets without differentiating any stored coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def CoefficientProbeFieldRegularity (D : ReferenceData) (f : PolarPoint → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ r θ, f (r, -θ) = f (r, θ)) ∧
    Function.Periodic f (0, Real.pi) ∧ ∀ p, p ∉ annularOpen D → f p = 0

theorem decodedCorrectionError_fieldRegularity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ)
    (r : CircleSpace S) (η : HeightPair S) :
    CoefficientProbeFieldRegularity D (decodedCorrectionError S L z r η) := by
  have hm : HeightMember D T (3 / 4 : ℝ) (decodedCorrectionError S L z r η) :=
    (hS.1 (3 / 4 : ℝ)).2.2.2.1 (L.error z r η).val
  exact ⟨(heightMember_contDiff_and_flatJets hT (by norm_num) hm).1,
    hm.2.1, hm.2.2.1, hm.2.2.2.1⟩

theorem coefficientErrorCrossNumerator_fieldRegularity
    {D : ReferenceData} {χ : ℝ → ℝ} {Er Ec Erc : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hr : CoefficientProbeFieldRegularity D Er)
    (hc : CoefficientProbeFieldRegularity D Ec)
    (hrc : CoefficientProbeFieldRegularity D Erc) :
    CoefficientProbeFieldRegularity D (coefficientErrorCrossNumerator χ Er Ec Erc) := by
  refine ⟨(hrc.1.sub ((contDiff_radialLinearProbe hχ).mul hc.1)).sub
      ((contDiff_radialCosineProbe hχ).mul hr.1), ?_, ?_, ?_⟩
  · intro r θ
    simp only [coefficientErrorCrossNumerator, radialLinearProbe_even,
      radialCosineProbe_even, hr.2.1 r θ, hc.2.1 r θ, hrc.2.1 r θ]
  · intro p
    change Erc (p + (0, Real.pi)) - radialLinearProbe χ (p + (0, Real.pi)) *
        Ec (p + (0, Real.pi)) - radialCosineProbe χ (p + (0, Real.pi)) *
          Er (p + (0, Real.pi)) = _
    rw [hrc.2.2.1 p, radialLinearProbe_periodic χ p, hc.2.2.1 p,
      radialCosineProbe_periodic χ p, hr.2.2.1 p]
  · intro p hp
    simp only [coefficientErrorCrossNumerator, hr.2.2.2 p hp,
      hc.2.2.2 p hp, hrc.2.2.2 p hp, mul_zero, sub_zero]

theorem coefficientErrorSquareNumerator_fieldRegularity
    {D : ReferenceData} {χ : ℝ → ℝ} {Ec Ecc : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : CoefficientProbeFieldRegularity D Ec)
    (hcc : CoefficientProbeFieldRegularity D Ecc) :
    CoefficientProbeFieldRegularity D (coefficientErrorSquareNumerator χ Ec Ecc) := by
  refine ⟨hcc.1.sub ((contDiff_const.mul (contDiff_radialCosineProbe hχ)).mul hc.1),
    ?_, ?_, ?_⟩
  · intro r θ
    simp only [coefficientErrorSquareNumerator, radialCosineProbe_even,
      hc.2.1 r θ, hcc.2.1 r θ]
  · intro p
    change Ecc (p + (0, Real.pi)) - 2 * radialCosineProbe χ (p + (0, Real.pi)) *
      Ec (p + (0, Real.pi)) = _
    rw [hcc.2.2.1 p, radialCosineProbe_periodic χ p, hc.2.2.1 p]
  · intro p hp
    simp only [coefficientErrorSquareNumerator, hc.2.2.2 p hp,
      hcc.2.2.2 p hp, mul_zero, sub_zero]

/-- Fixed angular interpolation removes exactly the two axis values. -/
def coefficientAxisNormalize (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  f p - f (p.1, 0) * Real.cos p.2 ^ 2 -
    f (p.1, Real.pi / 2) * Real.sin p.2 ^ 2

theorem coefficientAxisNormalize_fieldRegularity
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : CoefficientProbeFieldRegularity D f) :
    CoefficientProbeFieldRegularity D (coefficientAxisNormalize f) := by
  have h0 : ContDiff ℝ ∞ (fun p : PolarPoint => f (p.1, 0)) :=
    hf.1.comp (contDiff_fst.prodMk contDiff_const)
  have hhalf : ContDiff ℝ ∞ (fun p : PolarPoint => f (p.1, Real.pi / 2)) :=
    hf.1.comp (contDiff_fst.prodMk contDiff_const)
  refine ⟨(hf.1.sub (h0.mul (contDiff_snd.cos.pow 2))).sub
      (hhalf.mul (contDiff_snd.sin.pow 2)), ?_, ?_, ?_⟩
  · intro r θ
    simp only [coefficientAxisNormalize, hf.2.1 r θ, Real.cos_neg, Real.sin_neg, neg_sq]
  · intro p
    change f (p + (0, Real.pi)) - f (p.1 + 0, 0) * Real.cos (p.2 + Real.pi) ^ 2 -
      f (p.1 + 0, Real.pi / 2) * Real.sin (p.2 + Real.pi) ^ 2 = _
    rw [hf.2.2.1 p]
    simp only [coefficientAxisNormalize, add_zero, Real.cos_add_pi, Real.sin_add_pi, neg_sq]
  · intro p hp
    have h0 : (p.1, (0 : ℝ)) ∉ annularOpen D :=
      fun h => hp ⟨h.1, mem_univ _⟩
    have hhalf : (p.1, Real.pi / 2) ∉ annularOpen D :=
      fun h => hp ⟨h.1, mem_univ _⟩
    simp only [coefficientAxisNormalize, hf.2.2.2 p hp,
      hf.2.2.2 _ h0, hf.2.2.2 _ hhalf, zero_mul, sub_zero]

theorem coefficientAxisNormalize_axis_values (f : PolarPoint → ℝ) (r : ℝ) :
    coefficientAxisNormalize f (r, 0) = 0 ∧
      coefficientAxisNormalize f (r, Real.pi / 2) = 0 := by
  constructor <;> simp only [coefficientAxisNormalize, Real.cos_zero, Real.sin_zero,
    Real.cos_pi_div_two, Real.sin_pi_div_two, zero_pow two_ne_zero, one_pow,
    mul_one, mul_zero, sub_zero, sub_self]

/-- On an open radial region with the two zero values, every actual jet
is unchanged; no state-dependent cutoff or extension is chosen. -/
theorem coefficientAxisNormalize_eventuallyEq
    {f : PolarPoint → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hzero : ∀ r ∈ J, f (r, 0) = 0 ∧ f (r, Real.pi / 2) = 0)
    {p : PolarPoint} (hp : p.1 ∈ J) :
    coefficientAxisNormalize f =ᶠ[𝓝 p] f := by
  filter_upwards [(hJ.preimage continuous_fst).mem_nhds hp] with q hq
  simp only [coefficientAxisNormalize, (hzero q.1 hq).1, (hzero q.1 hq).2,
    zero_mul, sub_zero]

theorem coefficientAxisNormalize_mixedDerivative_eq
    {f : PolarPoint → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hzero : ∀ r ∈ J, f (r, 0) = 0 ∧ f (r, Real.pi / 2) = 0)
    {p : PolarPoint} (hp : p.1 ∈ J) (a b : ℕ) :
    mixedDerivative a b (coefficientAxisNormalize f) p = mixedDerivative a b f p :=
  mixedDerivative_eq_of_germ (coefficientAxisNormalize_eventuallyEq hJ hzero hp) a b

/-- These are actual angular jets of a genuinely smooth field. Reflection
and its periodic translate give the first zero jet at both centers. -/
theorem coefficientProbeField_axis_firstJets
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : CoefficientProbeFieldRegularity D f) (r : ℝ) :
    mixedDerivative 0 1 f (r, 0) = 0 ∧
      mixedDerivative 0 1 f (r, Real.pi / 2) = 0 := by
  have href := scalar_angularPartial_reflection (D := D) (σ := (1 : ℝ)) hf.1.contDiffOn
    (fun r θ => by simpa only [one_mul] using hf.2.1 r θ) hf.2.2.2
  have hz := href r 0
  simp only [neg_zero, neg_one_mul] at hz
  have hh := href r (Real.pi / 2)
  simp only [neg_one_mul] at hh
  have hperiod : angularPartial f (r, Real.pi / 2) =
      angularPartial f (r, -(Real.pi / 2)) := by
    simpa only [Prod.mk_add_mk, add_zero,
      show -(Real.pi / 2) + Real.pi = Real.pi / 2 by ring] using
      periodic_angularPartial hf.2.2.1 (r, -(Real.pi / 2))
  have hjet (θ : ℝ) : mixedDerivative 0 1 f (r, θ) = angularPartial f (r, θ) := by
    simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one] using
      (Radial.hasDerivAt_angularSlice (hf.1.differentiable (by simp) (r, θ))).deriv
  rw [hjet 0, hjet (Real.pi / 2)]
  constructor <;> linarith only [hz, hh, hperiod]

end ContinuousFlexibility.Analysis
