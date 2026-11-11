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
    (hzero : ∀ r ∉ Ioo (K.physicalLeft m) (K.physicalRight m),
      ∀ θ, u (r, θ) * f (r, θ) = 0)
    (hperiod : ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m),
      Function.Periodic (fun θ => u (r, θ) * f (r, θ)) Real.pi) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * f (r, θ))) =
      Real.pi⁻¹ * ∫ p, canonicalHeight S K z m u p * canonicalSource S K z m f p
        ∂canonicalMeasure S K m := by
  let Q : Set PolarPoint :=
    Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi
  let A : Set PolarPoint := Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi
  let g : PolarPoint → ℝ := fun p => u p * f p
  have hQm : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioc
  have hAm : MeasurableSet A := measurableSet_Ioo.prod measurableSet_Ioc
  have hQA : Q ⊆ A := fun p hp => ⟨(h04.2.2.2.1 m).2.2 hp.1, hp.2⟩
  have hQ : IntegrableOn g Q :=
    (n07a_canonical_pairing_integrable_iff h04 hz hs m u f).mp hi
  have houtside : ∀ p ∈ A \ Q, g p = 0 := by
    intro p hp
    exact hzero p.1 (fun hr => hp.2 ⟨hr, hp.1.2⟩) p.2
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
  have hAp : ∀ᵐ r ∂volume.restrict (Ioo D.a D.b),
      Function.Periodic (fun θ => g (r, θ)) Real.pi := by
    apply Eventually.of_forall
    intro r
    by_cases hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
    · exact hperiod r hr
    · intro θ
      exact (hzero r hr (θ + Real.pi)).trans (hzero r hr θ).symm
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
