import ContinuousFlexibility.Analysis.N06ReferenceModeTransport
import ContinuousFlexibility.Analysis.N06CanonicalGraphFourierCore
import ContinuousFlexibility.Radial.ReferenceCosineAlgebra

/-!
# The original finite height core uses the actual modal representatives

The normalized half-period cosine coefficient of a finite synthesis is
its literal radial coefficient. Thus any representatives of the actual
Fourier coefficients, including the C1/H2 representatives extracted from
the same N05 graph, reconstruct a finite-core height with the same finite
set of frequencies. No radial smoothness or finite raw forcing is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped BigOperators

/-- Exact coefficient recovery in the original half-period convention,
including the constant mode. Radial coefficients may be arbitrary. -/
theorem n06_halfCosineCoefficient_finiteSynthesis
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (i : ℕ) (r : ℝ) :
    n06HalfCosineCoefficient (r11bFiniteSynthesis s v referenceAngularBasis) i r =
      if i ∈ s then v i r else 0 := by
  have hc : Continuous (fun θ => r11bFiniteSynthesis s v referenceAngularBasis (r, θ)) := by
    unfold r11bFiniteSynthesis
    apply continuous_finsetSum s
    intro n _
    change Continuous (fun θ : ℝ => v n r * referenceAngularBasis n θ)
    exact continuous_const.mul (contDiff_referenceAngularBasis n).continuous
  have hp : Function.Periodic
      (fun θ => r11bFiniteSynthesis s v referenceAngularBasis (r, θ)) Real.pi := by
    intro θ
    unfold r11bFiniteSynthesis
    exact Finset.sum_congr rfl (fun n _ => congrArg (v n r * ·)
      (referenceAngularBasis_periodic n θ))
  have hi : IntervalIntegrable
      (fun θ => r11bFiniteSynthesis s v referenceAngularBasis (r, θ) * referenceAngularBasis i θ)
      volume 0 Real.pi := (hc.mul (contDiff_referenceAngularBasis i).continuous).intervalIntegrable _ _
  calc
    _ = angularMean (fun θ =>
        r11bFiniteSynthesis s v referenceAngularBasis (r, θ) * referenceAngularBasis i θ) := by
      simp only [n06HalfCosineCoefficient, n06AngularCoefficient, angleMeasure,
        angularMean, one_div, intervalIntegral.integral_of_le Real.pi_pos.le]
    _ = referenceAngularCoefficient
        (fun θ => r11bFiniteSynthesis s v referenceAngularBasis (r, θ)) i :=
      (n06_radialAngularMean_eq_angularMean (hp.mul (referenceAngularBasis_periodic i)) hi).symm
    _ = _ := referenceAngularCoefficient_sum_basis s (fun n => v n r) i

/-- Any representatives of the actual coefficients reconstruct the same
finite height. The original L2 class, measure and frequency set are kept. -/
theorem n06_finiteHeight_reconstruct_actual_modes
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U : CanonicalL2 S K m) (s : Finset ℕ) (a v : ℕ → ℝ → ℝ)
    (hU : (U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s a referenceAngularBasis)
    (hv : ∀ i ∈ s, n06HalfCosineCoefficient U i
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v i) :
    (U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s v referenceAngularBasis := by
  have hav (i : ℕ) (hi : i ∈ s) :
      a i =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v i := by
    have hc := n06_canonical_halfCosineCoefficient_congr_ae hU i
    have ha : n06HalfCosineCoefficient U i
        =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] a i := by
      filter_upwards [hc] with r hr
      simpa only [n06_halfCosineCoefficient_finiteSynthesis, if_pos hi] using hr
    exact ha.symm.trans (hv i hi)
  have hall : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      ∀ i ∈ s, a i r = v i r := (eventually_all_finset s).mpr hav
  have hp : ∀ᵐ p : PolarPoint ∂canonicalMeasure S K m, ∀ i ∈ s, a i p.1 = v i p.1 := by
    rw [n06_canonicalMeasure_eq_radial_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hall
  apply hU.trans
  filter_upwards [hp] with p hp
  unfold r11bFiniteSynthesis
  exact Finset.sum_congr rfl (fun i hi => congrArg (· * referenceAngularBasis i p.2) (hp i hi))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial

/-- The common finite set in the exact original graph core works for
any one chosen family of its actual modal representatives on all pieces. -/
theorem n06CanonicalGraphFiniteAngularCore_actual_modes
    {S : PhysicalSpacesData} {K : CanonicalData S} {Vol : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K Vol b} (u : B.Space)
    (hu : u ∈ n06CanonicalGraphFiniteAngularCore B) (v : ℕ → ℕ → ℝ → ℝ)
    (hv : ∀ m i, n06HalfCosineCoefficient (u.val.1.1 m) i
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v m i) :
    ∃ s : Finset ℕ, ∀ m, (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s (v m) referenceAngularBasis := by
  obtain ⟨s, a, _ha, hrep⟩ := hu
  exact ⟨s, fun m => n06_finiteHeight_reconstruct_actual_modes (u.val.1.1 m)
    s (a m) (v m) (hrep m) (fun i _ => hv m i)⟩

end ContinuousFlexibility.Statements
