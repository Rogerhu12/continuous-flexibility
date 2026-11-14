module

public import ContinuousFlexibility.Analysis.SobolevJetCompletion
public import Mathlib.Data.Fin.Embedding

/-!
# Compatibility of the Sobolev completions

Forgetting the higher derivatives is a contraction between the completed
Sobolev spaces.  It is the restriction of actual coordinate truncation on the
finite `L²` products.  Extensions of one fixed smooth-core map commute with
these bonding operators, so the extensions at all Sobolev orders form one
compatible family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ENNReal

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private def sobolevJetTruncateLinear (s : Set ℝ) {k m : ℕ} (hkm : k ≤ m) :
    SobolevJetAmbient F s m →ₗ[ℝ] SobolevJetAmbient F s k where
  toFun v := WithLp.toLp 2 (fun j ↦ v (Fin.castLE (Nat.succ_le_succ hkm) j))
  map_add' v w := by
    apply PiLp.ext
    intro j
    simp only [PiLp.toLp_apply, PiLp.add_apply]
  map_smul' c v := by
    apply PiLp.ext
    intro j
    simp only [PiLp.toLp_apply, PiLp.smul_apply, RingHom.id_apply]

private theorem sobolevJetTruncateLinear_apply (s : Set ℝ) {k m : ℕ} (hkm : k ≤ m)
    (v : SobolevJetAmbient F s m) (j : Fin (k + 1)) :
    sobolevJetTruncateLinear F s hkm v j = v (Fin.castLE (Nat.succ_le_succ hkm) j) :=
  PiLp.toLp_apply 2 (fun _ : Fin (k + 1) ↦ Lp F 2 (volume.restrict s))
    (fun i ↦ v (Fin.castLE (Nat.succ_le_succ hkm) i)) j

private theorem norm_sobolevJetTruncateLinear_le (s : Set ℝ) {k m : ℕ} (hkm : k ≤ m)
    (v : SobolevJetAmbient F s m) : ‖sobolevJetTruncateLinear F s hkm v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : Fin (k + 1), ‖sobolevJetTruncateLinear F s hkm v j‖ ^ 2) =
        ∑ j ∈ Finset.univ.map (Fin.castLEEmb (Nat.succ_le_succ hkm)), ‖v j‖ ^ 2 := by
      simp only [Finset.sum_map, Fin.castLEEmb_apply, sobolevJetTruncateLinear_apply]
    _ ≤ ∑ j : Fin (m + 1), ‖v j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)

/-- Actual coordinate truncation on the ambient finite `L²` product. -/
def sobolevJetTruncate (s : Set ℝ) {k m : ℕ} (hkm : k ≤ m) :
    SobolevJetAmbient F s m →L[ℝ] SobolevJetAmbient F s k :=
  (sobolevJetTruncateLinear F s hkm).mkContinuous 1 (fun v ↦ by
    simpa only [one_mul] using norm_sobolevJetTruncateLinear_le F s hkm v)

@[simp] theorem sobolevJetTruncate_apply (s : Set ℝ) {k m : ℕ} (hkm : k ≤ m)
    (v : SobolevJetAmbient F s m) (j : Fin (k + 1)) :
    sobolevJetTruncate F s hkm v j = v (Fin.castLE (Nat.succ_le_succ hkm) j) := by
  rw [sobolevJetTruncate, LinearMap.mkContinuous_apply]
  exact sobolevJetTruncateLinear_apply F s hkm v j

theorem norm_sobolevJetTruncate_le (s : Set ℝ) {k m : ℕ} (hkm : k ≤ m)
    (v : SobolevJetAmbient F s m) : ‖sobolevJetTruncate F s hkm v‖ ≤ ‖v‖ := by
  rw [sobolevJetTruncate, LinearMap.mkContinuous_apply]
  exact norm_sobolevJetTruncateLinear_le F s hkm v

theorem sobolevJetTruncate_core (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) {k m : ℕ} (hkm : k ≤ m)
    (f : smoothSobolevCore F s hs hu) :
    sobolevJetTruncate F s hkm (sobolevCoreJet F s hs hu m f) =
      sobolevCoreJet F s hs hu k f := by
  apply PiLp.ext
  intro j
  simp only [sobolevJetTruncate_apply, sobolevCoreJet_apply, Fin.val_castLE]

theorem norm_sobolevCoreJet_mono (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) {k m : ℕ} (hkm : k ≤ m)
    (f : smoothSobolevCore F s hs hu) :
    ‖sobolevCoreJet F s hs hu k f‖ ≤ ‖sobolevCoreJet F s hs hu m f‖ := by
  rw [← sobolevJetTruncate_core F s hs hu hkm f]
  exact norm_sobolevJetTruncate_le F s hkm _

/-- Continuous linear maps on a Sobolev completion are determined on the actual
smooth core. -/
theorem sobolevJetCompletion_continuousLinearMap_ext (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A B : SobolevJetCompletion F s hs hu k →L[ℝ] G)
    (h : ∀ f, A (coreToSobolevJet F s hs hu k f) = B (coreToSobolevJet F s hs hu k f)) :
    A = B := by
  have he : (A : SobolevJetCompletion F s hs hu k → G) = B :=
    (coreToSobolevJet_denseRange F s hs hu k).equalizer A.continuous B.continuous (funext h)
  exact ContinuousLinearMap.ext fun x ↦ congrFun he x

/-- The canonical contraction forgetting derivatives above order `k`. -/
def sobolevJetBonding (s : Set ℝ) (hs : MeasurableSet s) (hu : UniqueDiffOn ℝ s)
    {k m : ℕ} (hkm : k ≤ m) :
    SobolevJetCompletion F s hs hu m →L[ℝ] SobolevJetCompletion F s hs hu k :=
  (coreToSobolevJet F s hs hu k).extendOfNorm (coreToSobolevJet F s hs hu m)

@[simp] theorem sobolevJetBonding_apply_core (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) {k m : ℕ} (hkm : k ≤ m) (f : smoothSobolevCore F s hs hu) :
    sobolevJetBonding F s hs hu hkm (coreToSobolevJet F s hs hu m f) =
      coreToSobolevJet F s hs hu k f := by
  apply LinearMap.extendOfNorm_eq (coreToSobolevJet_denseRange F s hs hu m)
  refine ⟨1, fun g ↦ ?_⟩
  simpa only [norm_coreToSobolevJet, one_mul] using norm_sobolevCoreJet_mono F s hs hu hkm g

theorem norm_sobolevJetBonding_le (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) {k m : ℕ} (hkm : k ≤ m) :
    ‖sobolevJetBonding F s hs hu hkm‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (coreToSobolevJet_denseRange F s hs hu m) zero_le_one
  intro f
  simpa only [norm_coreToSobolevJet, one_mul] using norm_sobolevCoreJet_mono F s hs hu hkm f

/-- The completed bonding map really is coordinate truncation. -/
theorem sobolevJetBonding_coe (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) {k m : ℕ} (hkm : k ≤ m)
    (v : SobolevJetCompletion F s hs hu m) :
    (sobolevJetBonding F s hs hu hkm v : SobolevJetAmbient F s k) =
      sobolevJetTruncate F s hkm (v : SobolevJetAmbient F s m) := by
  have he : (fun u : SobolevJetCompletion F s hs hu m ↦
        (sobolevJetBonding F s hs hu hkm u : SobolevJetAmbient F s k)) =
      (fun u : SobolevJetCompletion F s hs hu m ↦
        sobolevJetTruncate F s hkm (u : SobolevJetAmbient F s m)) :=
    (coreToSobolevJet_denseRange F s hs hu m).equalizer
      (continuous_subtype_val.comp (sobolevJetBonding F s hs hu hkm).continuous)
      ((sobolevJetTruncate F s hkm).continuous.comp continuous_subtype_val) (by
        funext f
        simp only [Function.comp_apply, sobolevJetBonding_apply_core, coreToSobolevJet_coe,
          sobolevJetTruncate_core])
  exact congrFun he v

theorem sobolevJetBonding_refl (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) :
    sobolevJetBonding F s hs hu (le_refl k) =
      ContinuousLinearMap.id ℝ (SobolevJetCompletion F s hs hu k) := by
  apply sobolevJetCompletion_continuousLinearMap_ext F s hs hu k
  intro f
  simp only [sobolevJetBonding_apply_core, ContinuousLinearMap.id_apply]

theorem sobolevJetBonding_comp (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (sobolevJetBonding F s hs hu hkm).comp (sobolevJetBonding F s hs hu hmn) =
      sobolevJetBonding F s hs hu (hkm.trans hmn) := by
  apply sobolevJetCompletion_continuousLinearMap_ext F s hs hu n
  intro f
  simp only [ContinuousLinearMap.comp_apply, sobolevJetBonding_apply_core]

/-- Extensions of a fixed core map agree at different Sobolev orders. -/
theorem sobolevJetExtension_compatible {s t : Set ℝ} {hs : MeasurableSet s}
    {ht : MeasurableSet t} {hu : UniqueDiffOn ℝ s} {hv : UniqueDiffOn ℝ t}
    (E : smoothSobolevCore F s hs hu →ₗ[ℝ] smoothSobolevCore F t ht hv)
    {k m : ℕ} (hkm : k ≤ m) {Ck Cm : ℝ}
    (hk : ∀ f, ‖sobolevCoreJet F t ht hv k (E f)‖ ≤ Ck * ‖sobolevCoreJet F s hs hu k f‖)
    (hm : ∀ f, ‖sobolevCoreJet F t ht hv m (E f)‖ ≤ Cm * ‖sobolevCoreJet F s hs hu m f‖) :
    (sobolevJetBonding F t ht hv hkm).comp (sobolevJetExtension F E m) =
      (sobolevJetExtension F E k).comp (sobolevJetBonding F s hs hu hkm) := by
  apply sobolevJetCompletion_continuousLinearMap_ext F s hs hu m
  intro f
  simp only [ContinuousLinearMap.comp_apply, sobolevJetExtension_apply F E m hm,
    sobolevJetBonding_apply_core, sobolevJetExtension_apply F E k hk]

end ContinuousFlexibility.Analysis
