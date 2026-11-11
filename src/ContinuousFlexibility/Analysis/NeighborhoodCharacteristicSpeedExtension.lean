import ContinuousFlexibility.Analysis.NeighborhoodCharacteristicSpeed
import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
import Mathlib.Topology.Order.ProjIcc

/-!
# Extending the actual characteristic speed for the ordinary flow

Projection of the radial variable onto the closed control interval gives
a globally continuous speed and angular derivative. The speed agrees with
the original coefficients throughout that interval. Smoothness and angular
periodicity of the actual state height follow from the physical spaces.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

/-- Radial clamping supplies precisely the global inputs to the ordinary
flow theorem while leaving the original closed-strip speed unchanged. -/
theorem exists_extended_polarMinusCharacteristicSpeed
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {l h P : ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hl : 0 < l) (hlh : l ≤ h)
    (hadm : ∀ r ∈ Icc l h, ∀ θ,
      0 < polarDiscriminant w z (r, θ) ∧
      heightQ (profileEnergy w (r, θ)) (heightRadial z (r, θ))
        (angularPartial (heightAngular z) (r, θ)) ≠ 0)
    (hperiod : Function.Periodic z (0, P)) :
    ∃ G dG : PolarPoint → ℝ, Continuous G ∧ Continuous dG ∧
      (∀ r θ, HasDerivAt (fun t => G (r, t)) (dG (r, θ)) θ) ∧
      (∀ r, Function.Periodic (fun θ => G (r, θ)) P) ∧
      ∀ r ∈ Icc l h, ∀ θ,
        G (r, θ) = minusCharacteristicSpeed
          ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩ (r, θ) := by
  obtain ⟨d, hg, hd, hder⟩ :=
    exists_polarMinusCharacteristicSpeed_angularDerivative hw hz hl hadm
  let g : PolarPoint → ℝ := minusCharacteristicSpeed
    ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩
  let clamp : PolarPoint → PolarPoint :=
    fun p => ((projIcc l h hlh p.1 : ℝ), p.2)
  have hc : Continuous clamp :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
  have hmem (p : PolarPoint) : clamp p ∈ Icc l h ×ˢ (univ : Set ℝ) :=
    ⟨(projIcc l h hlh p.1).property, mem_univ p.2⟩
  refine ⟨g ∘ clamp, d ∘ clamp, hg.comp_continuous hc hmem,
    hd.comp_continuous hc hmem, ?_, ?_, ?_⟩
  · intro r θ
    exact hder (projIcc l h hlh r) (projIcc l h hlh r).property θ
  · intro r θ
    have hp := polarMinusCharacteristicSpeed_periodic w hperiod
      ((projIcc l h hlh r : ℝ), θ)
    simpa only [Function.comp_apply, clamp, g, Prod.mk_add_mk, add_zero] using hp
  · intro r hr θ
    simp only [Function.comp_apply, clamp, projIcc_of_mem hlh hr, g]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

theorem neighborhood_stateHeight_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {z : AnnularState S × ℝ} (hw : ContDiff ℝ ∞ (stateProfile D S C z.1)) :
    ContDiff ℝ ∞ (stateHeight D S C z) :=
  ((stateRadialHeight_contDiff_of_contDiff hw).comp contDiff_fst).add
    (contDiff_const.mul (neighborhood_stateU_contDiff hT hS z.1))

theorem neighborhood_stateHeight_periodic
    (hS : IsPhysicalSpaces D T S) (z : AnnularState S × ℝ) :
    Function.Periodic (stateHeight D S C z) (0, Real.pi) := by
  have hp := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1).2.2.1
  intro p
  simp only [stateHeight, stateU, heightPairField, Prod.fst_add, add_zero, hp p]

/-- Every actual state satisfying the already established profile and
denominator conditions supplies a global continuous, angularly C¹ speed.
No sector, sign-preservation, or supplied flow hypothesis is required. -/
theorem exists_stateCharacteristicSpeed_extension
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hC : controlGeometryConditions D S C)
    {z : AnnularState S × ℝ} (hw : ContDiff ℝ ∞ (stateProfile D S C z.1))
    (hadm : ∀ p ∈ annularOpen D,
      0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0)
    (m : ℕ) :
    ∃ G dG : PolarPoint → ℝ, Continuous G ∧ Continuous dG ∧
      (∀ r θ, HasDerivAt (fun t => G (r, t)) (dG (r, θ)) θ) ∧
      (∀ r, Function.Periodic (fun θ => G (r, θ)) Real.pi) ∧
      ∀ r ∈ Icc (C.left m) (C.right m), ∀ θ,
        G (r, θ) = minusCharacteristicSpeed (originalCoefficients D S C z) (r, θ) := by
  have hc := hC.1 m
  have hl : 0 < C.left m := lt_trans hD.choose_spec.1.1 hc.1
  have hstrip : ∀ r ∈ Icc (C.left m) (C.right m), ∀ θ,
      0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) (r, θ) ∧
      heightQ (profileEnergy (stateProfile D S C z.1) (r, θ))
        (heightRadial (stateHeight D S C z) (r, θ))
        (angularPartial (heightAngular (stateHeight D S C z)) (r, θ)) ≠ 0 := by
    intro r hr θ
    exact hadm (r, θ) ⟨⟨hc.1.trans_le hr.1, hr.2.trans_lt hc.2.2⟩, mem_univ θ⟩
  simpa only [originalCoefficients] using
    exists_extended_polarMinusCharacteristicSpeed hw
      (neighborhood_stateHeight_contDiff hT hS hw) hl hc.2.1.le hstrip
      (neighborhood_stateHeight_periodic hS z)

end ContinuousFlexibility.Statements
