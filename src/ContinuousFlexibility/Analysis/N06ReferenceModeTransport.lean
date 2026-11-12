import ContinuousFlexibility.Analysis.N06WeakCylinderPDE
import ContinuousFlexibility.Analysis.N06AngularMeanBridge
import ContinuousFlexibility.Analysis.N06ReferenceSourceJets
import ContinuousFlexibility.Radial.R11bFourierCoefficients

/-!
# Actual Fourier modes under the controlled reference chart

The half-period canonical coefficients and full-period physical
coefficients use the same normalized basis, including the mean. On the
actual radial reference chart, height conjugacy divides each mode by the
same radial height. Almost-everywhere changes of representatives preserve
these coefficients, so the identities apply to the original L2 fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n06_referenceAngularBasis_eq_evenCosineBasis (n : ℕ) :
    referenceAngularBasis n = evenCosineBasis n := by
  cases n with
  | zero => exact evenCosineBasis_zero.symm
  | succ n => exact (evenCosineBasis_of_ne_zero (Nat.succ_ne_zero n)).symm

/-- The mean and every positive normalized mode have the same coefficient
under the original full-period and canonical half-period conventions. -/
theorem n06_halfCosineCoefficient_eq_evenFourierCoefficient
    (η : PolarPoint → ℝ) (n : ℕ) (r : ℝ)
    (hp : Function.Periodic (fun θ => η (r, θ)) Real.pi)
    (hi : IntervalIntegrable (fun θ => η (r, θ) * referenceAngularBasis n θ)
      volume 0 Real.pi) :
    n06HalfCosineCoefficient η n r = evenFourierCoefficient η n r := by
  have hmean := n06_radialAngularMean_eq_angularMean
    (hp.mul (referenceAngularBasis_periodic n)) hi
  calc
    _ = angularMean (fun θ => η (r, θ) * referenceAngularBasis n θ) := by
      simp only [n06HalfCosineCoefficient, n06AngularCoefficient, angleMeasure,
        angularMean, one_div, intervalIntegral.integral_of_le Real.pi_pos.le]
    _ = radialAngularMean (fun θ => η (r, θ) * referenceAngularBasis n θ) := hmean.symm
    _ = _ := by
      simp only [n06_referenceAngularBasis_eq_evenCosineBasis, evenFourierCoefficient,
        angularPairing, angularAverage, radialAngularMean, one_div]

/-- Angular integration removes changes on a product null set, without
choosing a new coefficient or asking for pointwise representative equality. -/
theorem n06_halfCosineCoefficient_congr_ae {l r : ℝ} {U W : PolarPoint → ℝ}
    (hUW : U =ᵐ[(volume.restrict (Ioo l r)).prod angleMeasure] W) (n : ℕ) :
    n06HalfCosineCoefficient U n =ᵐ[volume.restrict (Ioo l r)]
      n06HalfCosineCoefficient W n := by
  filter_upwards [Measure.ae_ae_of_ae_prod hUW] with y hy
  unfold n06HalfCosineCoefficient n06AngularCoefficient
  apply congrArg (Real.pi⁻¹ * ·)
  apply integral_congr_ae
  filter_upwards [hy] with θ hθ
  exact congrArg (· * referenceAngularBasis n θ) hθ

theorem n06_canonical_halfCosineCoefficient_congr_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {U W : PolarPoint → ℝ} (hUW : U =ᵐ[canonicalMeasure S K m] W) (n : ℕ) :
    n06HalfCosineCoefficient U n =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))]
      n06HalfCosineCoefficient W n := by
  rw [n06_canonicalMeasure_eq_radial_prod] at hUW
  exact n06_halfCosineCoefficient_congr_ae hUW n

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The same actual reference chart transports the physical Fourier
coefficient by its literal height factor. No proposed inverse formula is
assumed: the inverse identities determine it at every angular value. -/
theorem n06_controlledReferenceHeight_mode
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (η : PolarPoint → ℝ) (m n : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m))
    (hp : Function.Periodic (fun θ => η (r, θ)) Real.pi)
    (hi : IntervalIntegrable (fun θ => η (r, θ) * referenceAngularBasis n θ)
      volume 0 Real.pi) :
    n06HalfCosineCoefficient (canonicalHeight S K (C.referenceState, 0) m η) n
        ((K.chart (C.referenceState, 0) m (r, 0)).1) =
      evenFourierCoefficient η n r / K.height (C.referenceState, 0) m (r, 0) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hcharts := h04.1.charts (C.referenceState, 0) href hs m
  rw [h04.1.referenceDomain m] at hcharts
  have hleft := hcharts.2.2.1
  let y := (K.chart (C.referenceState, 0) m (r, 0)).1
  let H := K.height (C.referenceState, 0) m (r, 0)
  have hinverse (θ : ℝ) : K.inverseChart (C.referenceState, 0) m (y, θ) = (r, θ) := by
    have hq : (r, θ) ∈ referencePhysicalPieceOpen S K m := ⟨hr, mem_univ θ⟩
    have hchart := (hcoordinates.1 m (r, θ) hq).1
    simpa only [hchart] using hleft (r, θ) hq
  have hheight (θ : ℝ) : canonicalHeight S K (C.referenceState, 0) m η (y, θ) =
      H⁻¹ * η (r, θ) := by
    have hq : (r, θ) ∈ referencePhysicalPieceOpen S K m := ⟨hr, mem_univ θ⟩
    simp only [canonicalHeight, hinverse θ, (hcoordinates.1 m (r, θ) hq).2]
    exact div_eq_inv_mul _ _
  change n06HalfCosineCoefficient (canonicalHeight S K (C.referenceState, 0) m η) n y =
    evenFourierCoefficient η n r / H
  calc
    _ = H⁻¹ * n06HalfCosineCoefficient η n r := by
      unfold n06HalfCosineCoefficient n06AngularCoefficient
      simp_rw [hheight, mul_assoc]
      rw [integral_const_mul]
      ring
    _ = _ := by
      rw [n06_halfCosineCoefficient_eq_evenFourierCoefficient η n r hp hi]
      exact (div_eq_inv_mul _ _).symm

end ContinuousFlexibility.Statements
