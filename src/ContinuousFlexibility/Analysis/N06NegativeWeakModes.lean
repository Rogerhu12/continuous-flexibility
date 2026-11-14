module

public import ContinuousFlexibility.Analysis.N06NegativeReferenceForcingLp
public import ContinuousFlexibility.Analysis.N06WeakCylinderPDE
public import ContinuousFlexibility.Analysis.N06WeakModeRegularity

/-!
# Actual weak negative modes on the recorded canonical interval

The same half-period cosine coefficients are extracted by the existing
canonical tensor pairing. The negative principal equation gives
`v'' + (2 n)^2 y v = g_n`. In the standard weak Sturm--Liouville convention
the coefficients are `a=1`, `c=-y`, `V=0` and the forcing is `-g_n`.

The last theorem obtains one family of C1 representatives from the same
original N05 graph. Their first derivatives are AC up to both recorded
endpoints and their second derivatives are L2. No modal equation or trace
matching condition is added to the original graph hypotheses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

theorem n06_canonical_halfCosineCoefficient_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U : CanonicalL2 S K m) (i : ℕ) :
    MemLp (n06HalfCosineCoefficient U i) 2
      (volume.restrict (Ioo (K.left m) (K.right m))) :=
  (n06_canonical_angularCoefficient_memLp U
    (memLp_angleMeasure_of_continuous (contDiff_referenceAngularBasis i).continuous)).const_mul
      Real.pi⁻¹

/-- The literal negative principal operator on the cosine tensor,
including the zero mode. -/
theorem n06_negativePrincipal_tensor {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i : ℕ) :
    n06NegativePrincipalTest (fun p => φ p.1 * referenceAngularBasis i p.2) =
      fun p => (deriv (deriv φ) p.1 + (((2 * i : ℕ) : ℝ)) ^ 2 * p.1 * φ p.1) *
        referenceAngularBasis i p.2 := by
  have he := contDiff_referenceAngularBasis i
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hed : ContDiff ℝ ∞ (deriv (referenceAngularBasis i)) :=
    (contDiff_infty_iff_deriv.mp he).2
  have hrr : radialPartial (radialPartial
      (fun p : PolarPoint => φ p.1 * referenceAngularBasis i p.2)) =
      fun p => deriv (deriv φ) p.1 * referenceAngularBasis i p.2 := by
    rw [n06_unit_radialPartial_tensor hφ he, n06_unit_radialPartial_tensor hφd he]
  have htt : angularPartial (angularPartial
      (fun p : PolarPoint => φ p.1 * referenceAngularBasis i p.2)) =
      fun p => φ p.1 * deriv (deriv (referenceAngularBasis i)) p.2 := by
    rw [n06_unit_angularPartial_tensor hφ he, n06_unit_angularPartial_tensor hφ hed]
  funext p
  unfold n06NegativePrincipalTest
  rw [hrr, htt]
  dsimp only
  rw [deriv_deriv_referenceAngularBasis]
  ring

/-- Fubini on the original canonical measure gives the exact normalized
radial mode equation on the actual interval, without rescaling it to unit
length. -/
theorem n06_negative_canonical_weak_modal
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hlr : K.left m ≤ K.right m) (U G : CanonicalL2 S K m)
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m) =
        ∫ p, G p * φ p ∂canonicalMeasure S K m) (i : ℕ) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (K.left m) (K.right m) →
        (∫ y in K.left m..K.right m, n06HalfCosineCoefficient U i y *
          (deriv (deriv φ) y + (((2 * i : ℕ) : ℝ)) ^ 2 * y * φ y)) =
          ∫ y in K.left m..K.right m, n06HalfCosineCoefficient G i y * φ y := by
  intro φ hφ hφc hφs
  let P : ℝ → ℝ := fun y => deriv (deriv φ) y + (((2 * i : ℕ) : ℝ)) ^ 2 * y * φ y
  have hP : Continuous P :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hφ).2).2).continuous.add
      ((continuous_const.mul continuous_id).mul hφ.continuous)
  have ht := n06_canonicalTest_tensor hφ hφc hφs
    (contDiff_referenceAngularBasis i) (referenceAngularBasis_periodic i)
  have he := hweak _ ht
  rw [n06_negativePrincipal_tensor hφ i] at he
  change (∫ p, U p * (P p.1 * referenceAngularBasis i p.2) ∂canonicalMeasure S K m) =
    ∫ p, G p * (φ p.1 * referenceAngularBasis i p.2) ∂canonicalMeasure S K m at he
  rw [n06_canonical_tensor_pairing U hP (contDiff_referenceAngularBasis i).continuous,
    n06_canonical_tensor_pairing G hφ.continuous (contDiff_referenceAngularBasis i).continuous] at he
  have hi : (∫ y in K.left m..K.right m,
      n06AngularCoefficient U (referenceAngularBasis i) y * P y) =
      ∫ y in K.left m..K.right m,
        n06AngularCoefficient G (referenceAngularBasis i) y * φ y := by
    simpa only [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo] using he
  change (∫ y in K.left m..K.right m,
    (Real.pi⁻¹ * n06AngularCoefficient U (referenceAngularBasis i) y) * P y) =
      ∫ y in K.left m..K.right m,
        (Real.pi⁻¹ * n06AngularCoefficient G (referenceAngularBasis i) y) * φ y
  calc
    _ = Real.pi⁻¹ * ∫ y in K.left m..K.right m,
        n06AngularCoefficient U (referenceAngularBasis i) y * P y := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring
    _ = Real.pi⁻¹ * ∫ y in K.left m..K.right m,
        n06AngularCoefficient G (referenceAngularBasis i) y * φ y := congrArg (Real.pi⁻¹ * ·) hi
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring

/-- The closed-interval H2 representative comes from the genuine modal
equation, with forcing `-g_n` in the standard weak-mode theorem. -/
theorem n06_negative_canonical_mode_regular
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hlr : K.left m < K.right m) (U G : CanonicalL2 S K m)
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m) =
        ∫ p, G p * φ p ∂canonicalMeasure S K m) (i : ℕ) :
    ∃ v : ℝ → ℝ,
      n06HalfCosineCoefficient U i =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v ∧
      ContDiff ℝ 1 v ∧
      AbsolutelyContinuousOnInterval (deriv v) (K.left m) (K.right m) ∧
      MemLp v 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
      MemLp (deriv v) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
      MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
      (∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
        deriv (deriv v) y + (((2 * i : ℕ) : ℝ)) ^ 2 * y * v y =
          n06HalfCosineCoefficient G i y) := by
  let j : ℝ := ((2 * i : ℕ) : ℝ)
  have hu := n06_canonical_halfCosineCoefficient_memLp U i
  have hg := n06_canonical_halfCosineCoefficient_memLp G i
  have hmodal := n06_negative_canonical_weak_modal hlr.le U G hweak i
  have hstandard : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (K.left m) (K.right m) →
        (∫ y in K.left m..K.right m, n06HalfCosineCoefficient U i y *
          (-deriv (fun t => (1 : ℝ) * deriv φ t) y + (j ^ 2 * (-y) + 0) * φ y)) =
          ∫ y in K.left m..K.right m, (-n06HalfCosineCoefficient G i y) * φ y := by
    intro φ hφ hφc hφs
    have he := hmodal φ hφ hφc hφs
    calc
      _ = -(∫ y in K.left m..K.right m, n06HalfCosineCoefficient U i y *
          (deriv (deriv φ) y + j ^ 2 * y * φ y)) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro y _
        simp only [one_mul, add_zero]
        ring
      _ = -(∫ y in K.left m..K.right m, n06HalfCosineCoefficient G i y * φ y) :=
        congrArg Neg.neg he
      _ = _ := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro y _
        ring
  obtain ⟨v, huv, hv, hvAC, hv₀, hv₁, hv₂, _, hode⟩ :=
    n06_weak_mode_L2_regular hlr (a := fun _ => (1 : ℝ)) (c := fun y => -y)
      (V := fun _ => (0 : ℝ)) j contDiff_const (by intro y hy; norm_num)
      continuous_id.neg continuous_const hu hg.neg hstandard
  refine ⟨v, huv, hv, hvAC, hv₀, hv₁, hv₂, ?_⟩
  filter_upwards [hode] with y hy
  simp only [Pi.neg_apply, one_mul, deriv_const, zero_mul, mul_zero, add_zero] at hy
  change deriv (deriv v) y + j ^ 2 * y * v y = n06HalfCosineCoefficient G i y
  nlinarith only [hy]

/-- One coherent family of negative modal representatives is obtained
from the same original graph. The L2 forcing is identified almost
everywhere with its actual source and scalar-column formula. -/
theorem n06N05_negative_modes_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false) :
    ∃ G : CanonicalL2 S K m,
      (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        n06NegativePrincipalForcing D S C K u.val.1
          (V.forget (3 / 4 : ℝ) 0 b u.val.2) m ∧
      ∃ v : ℕ → ℝ → ℝ, ∀ i : ℕ,
        n06HalfCosineCoefficient (u.val.1.1 m) i
          =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v i ∧
        ContDiff ℝ 1 (v i) ∧
        AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m) ∧
        MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
        MemLp (deriv (v i)) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
        MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
        (∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
          deriv (deriv (v i)) y + (((2 * i : ℕ) : ℝ)) ^ 2 * y * v i y =
            n06HalfCosineCoefficient G i y) := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  let g := n06NegativePrincipalForcing D S C K u.val.1
    (V.forget (3 / 4 : ℝ) 0 b u.val.2) m
  have hg : MemLp g 2 (canonicalMeasure S K m) :=
    n06N05_negativePrincipalForcing_memLp hT hS h u m hm
  let G : CanonicalL2 S K m := hg.toLp g
  have hG : (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] g := hg.coeFn_toLp
  have hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, u.val.1.1 m p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m) =
        ∫ p, G p * φ p ∂canonicalMeasure S K m := by
    intro φ hφ
    refine (n06N05_negative_principal_pairing hT hS h u m hm hφ).trans ?_
    apply integral_congr_ae
    filter_upwards [hG] with p hp
    rw [hp]
  choose v hv using fun i => n06_negative_canonical_mode_regular
    (h04.1.referenceBounds m).2.1 (u.val.1.1 m) G hweak i
  exact ⟨G, hG, v, hv⟩

end ContinuousFlexibility.Analysis
