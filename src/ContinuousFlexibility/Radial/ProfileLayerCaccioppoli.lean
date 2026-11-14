module

public import ContinuousFlexibility.Analysis.IntervalLayerEnergy
public import ContinuousFlexibility.Radial.ProfileLayerCoefficients
public import ContinuousFlexibility.Radial.ProfileLayerOverlap

/-!
# The actual profile equation on one endpoint layer

The coefficient constants depend on the profile alone. In particular the
Fourier parameter occurs only in the explicit factor `1 + j^2`.
-/

@[expose] public section

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

namespace ContinuousFlexibility.Radial

theorem profile_layer_caccioppoli_constants
    {D : ReferenceData} {C : ℕ → ℝ} (h : AccumulatingProfileBounds D C)
    (hC : 1 ≤ C 0) :
    ∃ A T : ℝ, 1 ≤ A ∧ 0 ≤ T ∧
      ∀ (j : ℝ) (u f : ℝ → ℝ) (x₀ q : ℝ),
      ContDiffOn ℝ 1 u (radialCore D) →
      MemLp u 2 (volume.restrict (radialCore D)) →
      MemLp f 2 (volume.restrict (radialCore D)) →
      x₀ ∈ radialCore D →
      (∀ r ∈ radialCore D, D.w r * deriv u r =
        intervalLocalPrimitive
          (fun y => f y + j ^ 2 * (deriv D.w y / y) * u y) x₀ r + q) →
      ∀ n : ℕ,
      (∫ r in profileEndpointLayer D (C 0) n,
        profileLayerCutoff D (C 0) n r ^ 2 * deriv u r ^ 2) ≤
        (7 * A ^ 4) * exp (4 * T * radialQ n) *
          ((∫ r in profileEndpointLayer D (C 0) n, f r ^ 2) +
            (1 + j ^ 2) * ∫ r in profileEndpointLayer D (C 0) n, u r ^ 2) := by
  obtain ⟨A, T, hA, hT, hcoeff⟩ := profile_layer_energy_constants h hC
  refine ⟨A, T, hA, hT, ?_⟩
  intro j u f x₀ q hu hu₂ hf hx₀ hflux n
  letI : IsFiniteMeasure (volume.restrict (radialCore D) : Measure ℝ) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      change volume (Ioo D.a D.b) < ⊤
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top⟩
  have hfloc : LocallyIntegrableOn f (radialCore D) volume :=
    IntegrableOn.locallyIntegrableOn (hf.integrable (by norm_num))
  have hwsmooth : ContDiff ℝ ∞ D.w := h.1.2.2.1.1
  have hwd : Continuous (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hwsmooth).2.continuous
  have hc : ContinuousOn (fun r => deriv D.w r / r) (radialCore D) :=
    hwd.continuousOn.div continuousOn_id
      (fun r hr => (h.1.1.trans hr.1).ne')
  have hsI := profileEndpointLayer_subset_core (D := D) (h.2.2.1 0) n
  have hfS : MemLp f 2 (volume.restrict (profileEndpointLayer D (C 0) n)) :=
    MemLp.mono_measure (Measure.restrict_mono hsI le_rfl) hf
  have huS : MemLp u 2 (volume.restrict (profileEndpointLayer D (C 0) n)) :=
    MemLp.mono_measure (Measure.restrict_mono hsI le_rfl) hu₂
  have hχ : ContDiff ℝ ∞ (profileLayerCutoff D (C 0) n) :=
    contDiff_intervalLayerCutoff _ _ _ _
  have hχc : HasCompactSupport (profileLayerCutoff D (C 0) n) :=
    hasCompactSupport_intervalLayerCutoff
      (profileLayerLower_pos (h.2.2.1 0) n) (profileLayerUpper_pos (h.2.2.1 0) n)
  have hb := interval_cutoff_caccioppoli_on_set h.1.2.1
    (measurableSet_profileEndpointLayer _ _ _) hsI hu hwsmooth.continuous.continuousOn hc
    hfloc hfS huS hχ hχc (tsupport_profileLayerCutoff_subset (h.2.2.1 0) n)
    (hcoeff n).1 (hcoeff n).1
    (fun r hr => by
      obtain ⟨hlo, hhi, hpot, hder⟩ := (hcoeff n).2 r hr
      have hχb := intervalLayerCutoff_bounds D.a D.b
        (profileLayerLower (C 0) n) (profileLayerUpper (C 0) n) r
      refine ⟨hlo, hhi, ?_, hder, hpot⟩
      change |intervalLayerCutoff D.a D.b
        (profileLayerLower (C 0) n) (profileLayerUpper (C 0) n) r| ≤ 1
      rw [abs_of_nonneg hχb.1]
      exact hχb.2)
    x₀ hx₀ q hflux
  have he : exp (4 * T * radialQ n) = exp (T * radialQ n) ^ 4 := by
    calc
      _ = exp (T * radialQ n + T * radialQ n + T * radialQ n + T * radialQ n) :=
        congrArg exp (by ring)
      _ = _ := by simp only [exp_add]; ring
  have hconst : 7 * (A * exp (T * radialQ n)) ^ 2 *
      (A * exp (T * radialQ n)) ^ 2 = (7 * A ^ 4) * exp (4 * T * radialQ n) := by
    rw [he]
    ring
  simpa only [hconst] using hb

end ContinuousFlexibility.Radial
