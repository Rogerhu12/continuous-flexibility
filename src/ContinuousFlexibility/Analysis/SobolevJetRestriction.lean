module

public import ContinuousFlexibility.Analysis.SobolevJetBonding

/-!
# Restriction and right inverses on the Sobolev completions

Restriction of a globally smooth Sobolev function retains the same function and
restricts the measure in each actual derivative norm.  It is therefore a
contraction at every Sobolev order.  A bounded core extension that preserves
values on the domain is a right inverse of this restriction after completion:
equality of values implies equality of every within-derivative on the domain,
and equality then passes from the dense smooth core to the completed spaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A globally smooth Sobolev function belongs to the intrinsic smooth core of
every measurable domain with unique within-derivatives. -/
theorem lineSobolevCore_le (s : Set ℝ) (hs : MeasurableSet s) (hu : UniqueDiffOn ℝ s) :
    LineSobolevCore F ≤ smoothSobolevCore F s hs hu := by
  intro f hf
  refine ⟨hf.1.mono (subset_univ s), fun n ↦ ?_⟩
  have he : iteratedDerivWithin n f s =ᵐ[volume.restrict s]
      iteratedDerivWithin n f univ := by
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [iteratedDerivWithin_univ]
    exact iteratedDerivWithin_eq_iteratedDeriv hu
      ((contDiffOn_univ.mp hf.1).contDiffAt.of_le (by simp)) hx
  exact (memLp_congr_ae he).mpr
    ((hf.2 n).mono_measure (Measure.restrict_mono_set volume (subset_univ s)))

/-- Actual restriction of smooth-core functions; the underlying function is
unchanged and only the domain of its Sobolev norms changes. -/
def sobolevCoreRestriction (s : Set ℝ) (hs : MeasurableSet s) (hu : UniqueDiffOn ℝ s) :
    LineSobolevCore F →ₗ[ℝ] smoothSobolevCore F s hs hu :=
  Submodule.inclusion (lineSobolevCore_le F s hs hu)

@[simp] theorem sobolevCoreRestriction_coe (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (f : LineSobolevCore F) :
    (sobolevCoreRestriction F s hs hu f : ℝ → F) = f :=
  Submodule.coe_inclusion _ f

theorem norm_sobolevCoreDerivative_restrict_le (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (n : ℕ) (f : LineSobolevCore F) :
    ‖sobolevCoreDerivative F s hs hu n (sobolevCoreRestriction F s hs hu f)‖ ≤
      ‖sobolevCoreDerivative F univ MeasurableSet.univ uniqueDiffOn_univ n f‖ := by
  rw [norm_sobolevCoreDerivative, norm_sobolevCoreDerivative, sobolevCoreRestriction_coe]
  have he : iteratedDerivWithin n f s =ᵐ[volume.restrict s]
      iteratedDerivWithin n f univ := by
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [iteratedDerivWithin_univ]
    exact iteratedDerivWithin_eq_iteratedDeriv hu
      ((contDiffOn_univ.mp f.property.1).contDiffAt.of_le (by simp)) hx
  rw [eLpNorm_congr_ae he]
  exact ENNReal.toReal_mono (f.property.2 n).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (subset_univ s)))

/-- Restriction is a contraction in the actual finite derivative Sobolev norm. -/
theorem norm_sobolevCoreJet_restrict_le (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) (f : LineSobolevCore F) :
    ‖sobolevCoreJet F s hs hu k (sobolevCoreRestriction F s hs hu f)‖ ≤
      ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _
  simp only [sobolevCoreJet_apply]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_sobolevCoreDerivative_restrict_le F s hs hu j.val f)

/-- Restriction from the whole-line Sobolev completion to the domain. -/
def sobolevRestriction (s : Set ℝ) (hs : MeasurableSet s) (hu : UniqueDiffOn ℝ s) (k : ℕ) :
    SobolevJetCompletion F univ MeasurableSet.univ uniqueDiffOn_univ k →L[ℝ]
      SobolevJetCompletion F s hs hu k :=
  sobolevJetExtension F (sobolevCoreRestriction F s hs hu) k

@[simp] theorem sobolevRestriction_apply_core (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) (f : LineSobolevCore F) :
    sobolevRestriction F s hs hu k
        (coreToSobolevJet F univ MeasurableSet.univ uniqueDiffOn_univ k f) =
      coreToSobolevJet F s hs hu k (sobolevCoreRestriction F s hs hu f) := by
  unfold sobolevRestriction
  exact sobolevJetExtension_apply F (sobolevCoreRestriction F s hs hu) k (C := 1)
    (fun g ↦ by simpa only [one_mul] using norm_sobolevCoreJet_restrict_le F s hs hu k g) f

theorem norm_sobolevRestriction_le (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) : ‖sobolevRestriction F s hs hu k‖ ≤ 1 := by
  apply norm_sobolevJetExtension_le F (sobolevCoreRestriction F s hs hu) k zero_le_one
  intro f
  simpa only [one_mul] using norm_sobolevCoreJet_restrict_le F s hs hu k f

/-- Equality on the domain is equality in every Sobolev completion, including
all of the actual derivative coordinates. -/
theorem coreToSobolevJet_congr (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) (f g : smoothSobolevCore F s hs hu)
    (hfg : EqOn (f : ℝ → F) g s) :
    coreToSobolevJet F s hs hu k f = coreToSobolevJet F s hs hu k g := by
  apply Subtype.ext
  rw [coreToSobolevJet_coe, coreToSobolevJet_coe]
  apply PiLp.ext
  intro j
  rw [sobolevCoreJet_apply, sobolevCoreJet_apply]
  unfold sobolevCoreDerivative
  exact MemLp.toLp_congr (f.property.2 j.val) (g.property.2 j.val) (by
    filter_upwards [ae_restrict_mem hs] with x hx
    exact iteratedDerivWithin_congr hfg hx)

/-- A bounded extension of the smooth core that retains values on the domain
is a genuine right inverse of completed Sobolev restriction. -/
theorem sobolevRestriction_comp_extension (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s)
    (E : smoothSobolevCore F s hs hu →ₗ[ℝ] LineSobolevCore F) (k : ℕ) {C : ℝ}
    (hbound : ∀ f,
      ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k (E f)‖ ≤
        C * ‖sobolevCoreJet F s hs hu k f‖)
    (hretain : ∀ (f : smoothSobolevCore F s hs hu) (x : ℝ), x ∈ s → E f x = f x) :
    (sobolevRestriction F s hs hu k).comp (sobolevJetExtension F E k) =
      ContinuousLinearMap.id ℝ (SobolevJetCompletion F s hs hu k) := by
  apply sobolevJetCompletion_continuousLinearMap_ext F s hs hu k
  intro f
  rw [ContinuousLinearMap.comp_apply, sobolevJetExtension_apply F E k hbound,
    sobolevRestriction_apply_core, ContinuousLinearMap.id_apply]
  apply coreToSobolevJet_congr
  intro x hx
  rw [sobolevCoreRestriction_coe]
  exact hretain f x hx

theorem sobolevRestriction_extension_apply (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s)
    (E : smoothSobolevCore F s hs hu →ₗ[ℝ] LineSobolevCore F) (k : ℕ) {C : ℝ}
    (hbound : ∀ f,
      ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k (E f)‖ ≤
        C * ‖sobolevCoreJet F s hs hu k f‖)
    (hretain : ∀ (f : smoothSobolevCore F s hs hu) (x : ℝ), x ∈ s → E f x = f x)
    (u : SobolevJetCompletion F s hs hu k) :
    sobolevRestriction F s hs hu k (sobolevJetExtension F E k u) = u := by
  have h := congrArg (fun A : SobolevJetCompletion F s hs hu k →L[ℝ]
      SobolevJetCompletion F s hs hu k ↦ A u)
    (sobolevRestriction_comp_extension F s hs hu E k hbound hretain)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

end ContinuousFlexibility.Analysis
