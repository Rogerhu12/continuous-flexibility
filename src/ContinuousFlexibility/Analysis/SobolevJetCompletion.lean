module

public import ContinuousFlexibility.Analysis.SmoothSobolevCore
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Sobolev completions of actual smooth jets

The order-`k` norm is the finite `ℓ²` sum of the actual `L²` norms of the
within-derivatives of orders zero through `k`.  Its completion is realized as the
closed linear span of these jets inside the corresponding finite product of
`L²` spaces.  Functions with zero Sobolev seminorm are thus identified without
introducing an extension-based quotient norm.

A single linear map on smooth cores with a bound in this norm extends to a
continuous linear map on each completed space.  The bound and agreement on the
smooth core are proved for the constructed operator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The finite product containing all actual derivatives through order `k`. -/
abbrev SobolevJetAmbient (s : Set ℝ) (k : ℕ) : Type _ :=
  PiLp 2 (fun _ : Fin (k + 1) ↦ Lp F 2 (volume.restrict s))

/-- One actual derivative, regarded as an `L²` element. -/
def sobolevCoreDerivative (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (n : ℕ) :
    smoothSobolevCore F s hs hu →ₗ[ℝ] Lp F 2 (volume.restrict s) where
  toFun f := (f.property.2 n).toLp (iteratedDerivWithin n f s)
  map_add' f g := by
    have he : iteratedDerivWithin n (↑(f + g) : ℝ → F) s =ᵐ[volume.restrict s]
        iteratedDerivWithin n f s + iteratedDerivWithin n g s := by
      filter_upwards [ae_restrict_mem hs] with x hx
      simp only [Submodule.coe_add, Pi.add_apply]
      exact iteratedDerivWithin_add hx hu ((f.property.1 x hx).of_le (by simp))
        ((g.property.1 x hx).of_le (by simp))
    exact (MemLp.toLp_congr ((f + g).property.2 n)
      ((f.property.2 n).add (g.property.2 n)) he).trans
        (MemLp.toLp_add (f.property.2 n) (g.property.2 n))
  map_smul' c f := by
    have he : iteratedDerivWithin n (↑(c • f) : ℝ → F) s =ᵐ[volume.restrict s]
        c • iteratedDerivWithin n f s := by
      filter_upwards [ae_restrict_mem hs] with x hx
      simp only [Submodule.coe_smul, Pi.smul_apply]
      exact iteratedDerivWithin_const_smul hx hu c ((f.property.1 x hx).of_le (by simp))
    exact (MemLp.toLp_congr ((c • f).property.2 n)
      ((f.property.2 n).const_smul c) he).trans
        (MemLp.toLp_const_smul c (f.property.2 n))

theorem sobolevCoreDerivative_ae (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (n : ℕ) (f : smoothSobolevCore F s hs hu) :
    (sobolevCoreDerivative F s hs hu n f : ℝ → F) =ᵐ[volume.restrict s]
      iteratedDerivWithin n f s :=
  MemLp.coeFn_toLp (f.property.2 n)

theorem norm_sobolevCoreDerivative (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (n : ℕ) (f : smoothSobolevCore F s hs hu) :
    ‖sobolevCoreDerivative F s hs hu n f‖ =
      (eLpNorm (iteratedDerivWithin n f s) 2 (volume.restrict s)).toReal :=
  Lp.norm_toLp (iteratedDerivWithin n f s) (f.property.2 n)

/-- The actual finite derivative jet as a linear map. -/
def sobolevCoreJet (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) :
    smoothSobolevCore F s hs hu →ₗ[ℝ] SobolevJetAmbient F s k where
  toFun f := WithLp.toLp 2 (fun j ↦ sobolevCoreDerivative F s hs hu j.val f)
  map_add' f g := by
    apply PiLp.ext
    intro j
    simp only [PiLp.toLp_apply, PiLp.add_apply, map_add]
  map_smul' c f := by
    apply PiLp.ext
    intro j
    simp only [PiLp.toLp_apply, PiLp.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem sobolevCoreJet_apply (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) (f : smoothSobolevCore F s hs hu)
    (j : Fin (k + 1)) :
    sobolevCoreJet F s hs hu k f j = sobolevCoreDerivative F s hs hu j.val f :=
  PiLp.toLp_apply 2 (fun _ : Fin (k + 1) ↦ Lp F 2 (volume.restrict s))
    (fun i ↦ sobolevCoreDerivative F s hs hu i.val f) j

/-- This is precisely the usual derivative Sobolev norm on the smooth core. -/
theorem norm_sobolevCoreJet_sq (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) (f : smoothSobolevCore F s hs hu) :
    ‖sobolevCoreJet F s hs hu k f‖ ^ 2 =
      ∑ j : Fin (k + 1),
        (eLpNorm (iteratedDerivWithin j.val f s) 2 (volume.restrict s)).toReal ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [sobolevCoreJet_apply, norm_sobolevCoreDerivative]

/-- The closed space of limits of actual smooth derivative jets. -/
def sobolevJetClosedSubmodule (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) : Submodule ℝ (SobolevJetAmbient F s k) :=
  (sobolevCoreJet F s hs hu k).range.topologicalClosure

/-- The derivative-norm Sobolev completion of the smooth core. -/
abbrev SobolevJetCompletion (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) : Type _ :=
  sobolevJetClosedSubmodule F s hs hu k

instance sobolevJetCompletion_completeSpace (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) : CompleteSpace (SobolevJetCompletion F s hs hu k) := by
  have hc : IsClosed (sobolevJetClosedSubmodule F s hs hu k : Set (SobolevJetAmbient F s k)) :=
    (sobolevCoreJet F s hs hu k).range.isClosed_topologicalClosure
  exact hc.isComplete.completeSpace_coe

theorem sobolevJetClosedSubmodule_coe (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) :
    (sobolevJetClosedSubmodule F s hs hu k : Set (SobolevJetAmbient F s k)) =
      closure (Set.range (sobolevCoreJet F s hs hu k)) := by
  rw [sobolevJetClosedSubmodule, Submodule.topologicalClosure_coe, LinearMap.coe_range]

/-- The canonical dense map of the smooth core into its Sobolev completion. -/
def coreToSobolevJet (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) :
    smoothSobolevCore F s hs hu →ₗ[ℝ] SobolevJetCompletion F s hs hu k :=
  (sobolevCoreJet F s hs hu k).codRestrict _ (fun f ↦
    (sobolevCoreJet F s hs hu k).range.le_topologicalClosure
      (LinearMap.mem_range_self _ f))

@[simp] theorem coreToSobolevJet_coe (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) (f : smoothSobolevCore F s hs hu) :
    (coreToSobolevJet F s hs hu k f : SobolevJetAmbient F s k) =
      sobolevCoreJet F s hs hu k f :=
  LinearMap.codRestrict_apply _ _ _

@[simp] theorem norm_coreToSobolevJet (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) (f : smoothSobolevCore F s hs hu) :
    ‖coreToSobolevJet F s hs hu k f‖ = ‖sobolevCoreJet F s hs hu k f‖ := by
  calc
    ‖coreToSobolevJet F s hs hu k f‖ =
        ‖(coreToSobolevJet F s hs hu k f : SobolevJetAmbient F s k)‖ :=
      (Submodule.norm_coe _).symm
    _ = ‖sobolevCoreJet F s hs hu k f‖ :=
      congrArg norm (coreToSobolevJet_coe F s hs hu k f)

theorem coreToSobolevJet_denseRange (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) (k : ℕ) : DenseRange (coreToSobolevJet F s hs hu k) := by
  rw [DenseRange, Subtype.dense_iff]
  have hi : Subtype.val '' Set.range (coreToSobolevJet F s hs hu k) =
      Set.range (sobolevCoreJet F s hs hu k) := by
    ext v
    constructor
    · rintro ⟨w, ⟨f, rfl⟩, rfl⟩
      exact ⟨f, (coreToSobolevJet_coe F s hs hu k f).symm⟩
    · rintro ⟨f, rfl⟩
      exact ⟨coreToSobolevJet F s hs hu k f, ⟨f, rfl⟩,
        coreToSobolevJet_coe F s hs hu k f⟩
  intro v hv
  exact Eq.mpr (congrArg (fun A : Set (SobolevJetAmbient F s k) ↦ v ∈ closure A) hi)
    ((sobolevJetClosedSubmodule_coe F s hs hu k).subset hv)

variable {s t : Set ℝ} {hs : MeasurableSet s} {ht : MeasurableSet t}
  {hu : UniqueDiffOn ℝ s} {hv : UniqueDiffOn ℝ t}

/-- Bounds on the actual individual derivatives give a bound on the finite
Sobolev norm.  This form also accommodates lower-order cutoff terms. -/
theorem sobolevCoreJet_norm_le_of_coordinate_bounds
    (E : smoothSobolevCore F s hs hu →ₗ[ℝ] smoothSobolevCore F t ht hv)
    (k : ℕ) (C : Fin (k + 1) → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hbound : ∀ (j : Fin (k + 1)) (f : smoothSobolevCore F s hs hu),
      ‖sobolevCoreDerivative F t ht hv j.val (E f)‖ ≤ C j * ‖sobolevCoreJet F s hs hu k f‖)
    (f : smoothSobolevCore F s hs hu) :
    ‖sobolevCoreJet F t ht hv k (E f)‖ ≤
      (∑ j, C j) * ‖sobolevCoreJet F s hs hu k f‖ := by
  have hnonneg : 0 ≤ (∑ j, C j) * ‖sobolevCoreJet F s hs hu k f‖ :=
    mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC j) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hnonneg).mp
  calc
    ‖sobolevCoreJet F t ht hv k (E f)‖ ^ 2 =
        ∑ j : Fin (k + 1), ‖sobolevCoreDerivative F t ht hv j.val (E f)‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [sobolevCoreJet_apply]
    _ ≤ ∑ j : Fin (k + 1), (C j * ‖sobolevCoreJet F s hs hu k f‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hC j) (norm_nonneg _))).mpr (hbound j f)
    _ ≤ (∑ j : Fin (k + 1), C j * ‖sobolevCoreJet F s hs hu k f‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ ↦ mul_nonneg (hC j) (norm_nonneg _))
    _ = ((∑ j, C j) * ‖sobolevCoreJet F s hs hu k f‖) ^ 2 := by rw [Finset.sum_mul]

/-- The actual bounded extension of a single core map at Sobolev order `k`.
Its construction does not choose a new map on smooth functions at each order. -/
def sobolevJetExtension
    (E : smoothSobolevCore F s hs hu →ₗ[ℝ] smoothSobolevCore F t ht hv) (k : ℕ) :
    SobolevJetCompletion F s hs hu k →L[ℝ] SobolevJetCompletion F t ht hv k :=
  ((coreToSobolevJet F t ht hv k).comp E).extendOfNorm (coreToSobolevJet F s hs hu k)

theorem sobolevJetExtension_apply
    (E : smoothSobolevCore F s hs hu →ₗ[ℝ] smoothSobolevCore F t ht hv)
    (k : ℕ) {C : ℝ}
    (hbound : ∀ f, ‖sobolevCoreJet F t ht hv k (E f)‖ ≤ C * ‖sobolevCoreJet F s hs hu k f‖)
    (f : smoothSobolevCore F s hs hu) :
    sobolevJetExtension F E k (coreToSobolevJet F s hs hu k f) =
      coreToSobolevJet F t ht hv k (E f) := by
  apply LinearMap.extendOfNorm_eq (coreToSobolevJet_denseRange F s hs hu k)
  refine ⟨C, fun g ↦ ?_⟩
  simpa only [LinearMap.comp_apply, norm_coreToSobolevJet] using hbound g

theorem norm_sobolevJetExtension_le
    (E : smoothSobolevCore F s hs hu →ₗ[ℝ] smoothSobolevCore F t ht hv)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f, ‖sobolevCoreJet F t ht hv k (E f)‖ ≤ C * ‖sobolevCoreJet F s hs hu k f‖) :
    ‖sobolevJetExtension F E k‖ ≤ C := by
  apply LinearMap.opNorm_extendOfNorm_le (coreToSobolevJet_denseRange F s hs hu k) hC
  intro f
  simpa only [LinearMap.comp_apply, norm_coreToSobolevJet] using hbound f

/-- Agreement on the genuine smooth core determines the completed operator. -/
theorem sobolevJetExtension_unique
    (E : smoothSobolevCore F s hs hu →ₗ[ℝ] smoothSobolevCore F t ht hv)
    (k : ℕ) {C : ℝ}
    (hbound : ∀ f, ‖sobolevCoreJet F t ht hv k (E f)‖ ≤ C * ‖sobolevCoreJet F s hs hu k f‖)
    (B : SobolevJetCompletion F s hs hu k →L[ℝ] SobolevJetCompletion F t ht hv k)
    (hB : ∀ f, B (coreToSobolevJet F s hs hu k f) = coreToSobolevJet F t ht hv k (E f)) :
    sobolevJetExtension F E k = B := by
  have he : (sobolevJetExtension F E k : SobolevJetCompletion F s hs hu k →
        SobolevJetCompletion F t ht hv k) = B :=
    (coreToSobolevJet_denseRange F s hs hu k).equalizer
      (sobolevJetExtension F E k).continuous B.continuous
      (funext fun f ↦ (sobolevJetExtension_apply F E k hbound f).trans (hB f).symm)
  exact ContinuousLinearMap.ext fun x ↦ congrFun he x

end ContinuousFlexibility.Analysis
