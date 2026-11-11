import ContinuousFlexibility.Analysis.N06AngularMeanBridge
import ContinuousFlexibility.Analysis.CanonicalSourceConversion
import ContinuousFlexibility.Radial.R11bPhysicalPairing

/-!
# Physical weak pairings on the actual canonical half-period

The full physical angular mean agrees with the half-period integral for
periodic integrands. Actual integrability is retained when applying Fubini.
A function supported on one physical piece can then be paired in the
original canonical measure by the genuine coordinate change.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem n06_physicalMean_eq_halfIntegral
    {D : ReferenceData} (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hperiod : Function.Periodic f (0, Real.pi))
    (hf : IntegrableOn f (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      Real.pi⁻¹ * ∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, f p := by
  have hmeasure : volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) =
      (volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
    change ((volume : Measure ℝ).prod volume).restrict _ = _
    rw [← Measure.prod_restrict]
  have hprod : Integrable f ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) Real.pi))) := by
    rwa [IntegrableOn, hmeasure] at hf
  have hmean : (fun r => radialAngularMean (fun θ => f (r, θ))) =ᵐ[
      volume.restrict (radialCore D)]
      (fun r => angularMean (fun θ => f (r, θ))) := by
    filter_upwards [hprod.prod_right_ae] with r hr
    apply n06_radialAngularMean_eq_angularMean
    · intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hperiod (r, θ)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr hr
  have hrad : (volume : Measure ℝ).restrict (radialCore D) =
      volume.restrict (Ioc D.a D.b) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
  calc
    _ = ∫ r in D.a..D.b, angularMean (fun θ => f (r, θ)) := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      rw [hrad] at hmean
      exact integral_congr_ae hmean
    _ = _ := by
      unfold angularMean
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hab]
      simp_rw [intervalIntegral.integral_of_le Real.pi_pos.le]
      rw [← hrad, hmeasure, integral_prod _ hprod]
      rw [one_div]

theorem n06_physicalHalfIntegral_eq_piece
    {D : ReferenceData} {S : PhysicalSpacesData} {K : CanonicalData S}
    (m : ℕ) (hpiece : Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    {f : PolarPoint → ℝ}
    (hzero : ∀ p, p ∉ physicalPieceOpen S K m → f p = 0) :
    (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, f p) =
      ∫ p in physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), f p := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_Ioo.prod measurableSet_Ioc)
  · intro p hp
    exact ⟨hpiece hp.1.1, hp.2.2⟩
  · intro p hp
    apply hzero p
    intro hpm
    exact hp.2 ⟨hpm, mem_univ _, hp.1.2⟩

/-- The full-period physical pairing becomes the original half-period
canonical pairing, with its exact normalization and unchanged fields. -/
theorem n06_physicalMean_pairing_eq_canonical
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε) (hab : D.a ≤ D.b)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (u f : PolarPoint → ℝ)
    (hperiod : Function.Periodic (fun p => u p * f p) (0, Real.pi))
    (hint : IntegrableOn (fun p => u p * f p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi))
    (hzero : ∀ p, p ∉ physicalPieceOpen S K m → u p * f p = 0) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * f (r, θ))) =
      Real.pi⁻¹ * ∫ p, canonicalHeight S K z m u p * canonicalSource S K z m f p
        ∂canonicalMeasure S K m := by
  rw [n06_physicalMean_eq_halfIntegral hab hperiod hint,
    n06_physicalHalfIntegral_eq_piece m (hK.2.2.2.1 m).2.2 hzero,
    canonicalSource_pairing_of_partA hK hz hs m u f]
  simp only [canonicalMeasure, canonicalOpen, prod_inter_prod, inter_univ, univ_inter]

end ContinuousFlexibility.Statements
