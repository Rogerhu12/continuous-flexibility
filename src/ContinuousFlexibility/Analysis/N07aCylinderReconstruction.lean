module

public import ContinuousFlexibility.Analysis.SpacesPhysicalReconstruction

/-!
# Smooth reconstruction from the actual unweighted cylinder jets

The canonical bootstrap first produces L² weak derivatives. After a
compact radial localization, this version of the existing mollification
argument reconstructs a smooth function directly from those derivatives,
before packing any material grading or physical projective limit.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Convolution
open ContinuousFlexibility.Statements

def n07aCylinderMollification (u : CylinderL2) (n : ℕ) : PolarPoint → ℝ :=
  planarConvolution (cylinderPeriodicExtension u) ((spacesMollifierBump n).normed volume)

theorem n07aCylinderMollification_contDiff (u : CylinderL2) (n : ℕ) :
    ContDiff ℝ ∞ (n07aCylinderMollification u n) :=
  contDiff_planarConvolution (locallyIntegrable_cylinderPeriodicExtension u)
    (spacesMollifierBump n).contDiff_normed (spacesMollifierBump n).hasCompactSupport_normed

theorem n07aCylinderMollification_periodic (u : CylinderL2) (n : ℕ) :
    Function.Periodic (n07aCylinderMollification u n) (0, Real.pi) :=
  planarConvolution_periodic_left (cylinderPeriodicExtension_periodic u)

theorem n07aCylinderMollification_mixedDerivative
    {u d : CylinderL2} {a b : ℕ} (hd : HasWeakMixedDerivative u d a b) (n : ℕ) :
    mixedDerivative a b (n07aCylinderMollification u n) =
      (spacesMollifierBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        cylinderPeriodicExtension d := by
  rw [n07aCylinderMollification,
    hd.periodicConvolution (spacesMollifierBump n).contDiff_normed
      (spacesMollifierBump n).hasCompactSupport_normed,
    spaces_planarConvolution_eq_left]

/-- Actual cylinder weak jets reconstruct a genuine smooth periodic
representative, with each classical derivative agreeing with its original
L² class. No smooth representative is supplied as an input. -/
theorem n07a_exists_smooth_cylinderRepresentative (u : CylinderL2)
    (d : ℕ → ℕ → CylinderL2) (hd : ∀ a b, HasWeakMixedDerivative u (d a b) a b) :
    ∃ v : PolarPoint → ℝ, ContDiff ℝ ∞ v ∧ Function.Periodic v (0, Real.pi) ∧
      (∀ a b, mixedDerivative a b v =ᵐ[materialCylinderMeasure] (d a b : PolarPoint → ℝ)) ∧
      ∀ a b, TendstoLocallyUniformly
        (fun n => mixedDerivative a b (n07aCylinderMollification u n))
        (mixedDerivative a b v) atTop := by
  have hlim (a b : ℕ) (Q : Set PolarPoint) (hQ : IsCompact Q) :
      Tendsto (fun n => ∫ p in Q,
        |mixedDerivative a b (n07aCylinderMollification u n) p -
          cylinderPeriodicExtension (d a b) p|) atTop (𝓝 0) := by
    simp_rw [n07aCylinderMollification_mixedDerivative (hd a b)]
    exact spaces_tendsto_setIntegral_abs_bump_convolution_sub spacesMollifierBump_tendsto
      (locallyIntegrable_cylinderPeriodicExtension _) hQ
  have hp (n : ℕ) (x : ℝ) :
      Function.Periodic (fun θ => n07aCylinderMollification u n (x, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using n07aCylinderMollification_periodic u n (x, θ)
  obtain ⟨v, hv, hvp, hvl⟩ := spaces_exists_smooth_periodic_of_local_L1_jets
    (n07aCylinderMollification u) (fun a b => cylinderPeriodicExtension (d a b))
    (n07aCylinderMollification_contDiff u) hp
    (fun _ _ => locallyIntegrable_cylinderPeriodicExtension _) hlim
  refine ⟨v, hv, hvp, ?_, hvl⟩
  intro a b
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    spacesMollifierBump_tendsto (Eventually.of_forall spacesMollifierBump_ratio)
    (locallyIntegrable_cylinderPeriodicExtension (d a b))
  have hplane : mixedDerivative a b v =ᵐ[volume] cylinderPeriodicExtension (d a b) := by
    filter_upwards [hae] with p hp
    have hpoint := (hvl a b).tendstoLocallyUniformlyOn.tendsto_at (mem_univ p)
    simp_rw [n07aCylinderMollification_mixedDerivative (hd a b)] at hpoint
    exact tendsto_nhds_unique hpoint hp
  exact (hplane.filter_mono (ae_mono Measure.restrict_le_self)).trans
    (cylinderPeriodicExtension_ae _)

end ContinuousFlexibility.Analysis
