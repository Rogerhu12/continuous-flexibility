import ContinuousFlexibility.Analysis.N07aCanonicalRoughPairing
import ContinuousFlexibility.Analysis.N07aPeriodicRadialPairing

/-!
# A localized rough physical pairing with its exact normalization

The integrability premise is on the actual transformed paired functions.
The chart proves physical integrability; compact test support then extends
it to the annulus before the physical full-period mean is evaluated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07a_localized_rough_pairing
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u f : PolarPoint → ℝ)
    (hi : Integrable (fun p => canonicalHeight S K z m u p *
      canonicalSource S K z m f p) (canonicalMeasure S K m))
    (hzero : ∀ p ∉ physicalPieceOpen S K z m, u p * f p = 0)
    (hperiod : ∀ p ∈ physicalPieceOpen S K z m,
      u (p + (0, Real.pi)) * f (p + (0, Real.pi)) = u p * f p) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * f (r, θ))) =
      Real.pi⁻¹ * ∫ p, canonicalHeight S K z m u p * canonicalSource S K z m f p
        ∂canonicalMeasure S K m := by
  let Q : Set PolarPoint :=
    physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)
  let A : Set PolarPoint := Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi
  let g : PolarPoint → ℝ := fun p => u p * f p
  have hdomain := h04.1.domains z hz hs m
  have hQm : MeasurableSet Q := hdomain.1.measurableSet.inter
    (MeasurableSet.univ.prod measurableSet_Ioc)
  have hAm : MeasurableSet A := measurableSet_Ioo.prod measurableSet_Ioc
  have hQA : Q ⊆ A := fun p hp => ⟨(hdomain.2.2.1 hp.1).1, hp.2.2⟩
  have hQ : IntegrableOn g Q :=
    (n07a_canonical_pairing_integrable_iff h04 hz hs m u f).mp hi
  have houtside : ∀ p ∈ A \ Q, g p = 0 := by
    intro p hp
    exact hzero p (fun hOmega => hp.2 ⟨hOmega, mem_univ _, hp.1.2⟩)
  have hzeroAE : g =ᵐ[volume.restrict (A \ Q)] fun _ => 0 :=
    (ae_restrict_mem (hAm.diff hQm)).mono houtside
  have hdiff : IntegrableOn g (A \ Q) := (integrable_congr hzeroAE).mpr (integrable_zero _ _ _)
  have hA : IntegrableOn g A := (hQ.union hdiff).mono_set (by
    intro p hp
    by_cases h : p ∈ Q
    · exact Or.inl h
    · exact Or.inr ⟨hp, h⟩)
  have hmeasure : (volume.restrict (Ioo D.a D.b)).prod angleMeasure =
      volume.restrict A := by
    rw [angleMeasure, Measure.prod_restrict]
    rfl
  have hperiodic : Function.Periodic g (0, Real.pi) := by
    intro p
    by_cases hp : p ∈ physicalPieceOpen S K z m
    · exact hperiod p hp
    · have hps : p + (0, Real.pi) ∉ physicalPieceOpen S K z m :=
        fun h => hp ((hdomain.2.2.2.1 p).mp h)
      exact (hzero _ hps).trans (hzero _ hp).symm
  have hAp : ∀ᵐ r ∂volume.restrict (Ioo D.a D.b),
      Function.Periodic (fun theta => g (r, theta)) Real.pi := by
    apply Eventually.of_forall
    intro r theta
    simpa only [Prod.mk_add_mk, add_zero] using hperiodic (r, theta)
  have hhalf := n07a_periodic_radial_mean_eq_half hab
    (show Integrable g ((volume.restrict (Ioo D.a D.b)).prod angleMeasure) by
      rw [hmeasure]; exact hA) hAp
  rw [hmeasure] at hhalf
  calc
    _ = Real.pi⁻¹ * ∫ p in A, g p := hhalf
    _ = Real.pi⁻¹ * ∫ p in Q, g p := congrArg (Real.pi⁻¹ * ·)
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hAm hQA houtside)
    _ = _ := congrArg (Real.pi⁻¹ * ·) (n07a_canonical_pairing_all h04 hz hs m u f)

end ContinuousFlexibility.Analysis
