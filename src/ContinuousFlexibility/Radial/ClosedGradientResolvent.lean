import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith

/-!
# The positive resolvent of a closed gradient relation

A closed linear relation between a function and its derivative is a closed
subspace of the Hilbert product. Projection of `(f, 0)` onto this subspace
constructs the resolvent at `-1`, without a spectral theorem and without a
choice of representatives. Increasing closed gradient spaces give strongly
convergent positive resolvents.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Hilbert product containing a function and its derivative. -/
abbrev GradientHilbert (H : Type*) [NormedAddCommGroup H] := WithLp 2 (H × H)

/-- Put a forcing term in the function coordinate of the Hilbert product. -/
def gradientInjection : H →L[ℝ] GradientHilbert H :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℝ H H

theorem gradientInjection_apply (f : H) :
    gradientInjection f = WithLp.toLp 2 (f, 0) := by
  simp only [gradientInjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.inl_apply,
    WithLp.prodContinuousLinearEquiv_symm_apply]

/-- The function and derivative coordinates of the positive resolvent. -/
def closedGradientResolventPair (K : ClosedSubmodule ℝ (GradientHilbert H)) :
    H →L[ℝ] GradientHilbert H :=
  K.toSubmodule.starProjection ∘L gradientInjection

/-- The positive resolvent on the function coordinate. -/
def closedGradientResolvent (K : ClosedSubmodule ℝ (GradientHilbert H)) : H →L[ℝ] H :=
  WithLp.fstL 2 ℝ H H ∘L closedGradientResolventPair K

theorem closedGradientResolventPair_apply
    (K : ClosedSubmodule ℝ (GradientHilbert H)) (f : H) :
    closedGradientResolventPair K f = K.toSubmodule.starProjection (gradientInjection f) := by
  simp only [closedGradientResolventPair, ContinuousLinearMap.comp_apply]

theorem closedGradientResolvent_apply
    (K : ClosedSubmodule ℝ (GradientHilbert H)) (f : H) :
    closedGradientResolvent K f = (closedGradientResolventPair K f).fst := by
  simp only [closedGradientResolvent, ContinuousLinearMap.comp_apply, WithLp.fstL_apply]

theorem closedGradientResolventPair_mem
    (K : ClosedSubmodule ℝ (GradientHilbert H)) (f : H) :
    closedGradientResolventPair K f ∈ K := by
  rw [closedGradientResolventPair_apply]
  exact K.toSubmodule.starProjection_apply_mem _

/-- The operator graph represented by a closed gradient relation. -/
def ClosedGradientGraph (K : ClosedSubmodule ℝ (GradientHilbert H)) (u f : H) : Prop :=
  ∃ q : GradientHilbert H, q ∈ K ∧ q.fst = u ∧
    ∀ r ∈ K, ⟪f, r.fst⟫_ℝ = ⟪q.snd, r.snd⟫_ℝ

theorem closedGradientResolvent_graph
    (K : ClosedSubmodule ℝ (GradientHilbert H)) (f : H) :
    ClosedGradientGraph K (closedGradientResolvent K f)
      (f - closedGradientResolvent K f) := by
  refine ⟨closedGradientResolventPair K f, closedGradientResolventPair_mem K f,
    (closedGradientResolvent_apply K f).symm, ?_⟩
  intro r hr
  have h := K.toSubmodule.starProjection_inner_eq_zero (gradientInjection f) r hr
  rw [← closedGradientResolventPair_apply] at h
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    WithLp.sub_fst, WithLp.sub_snd, gradientInjection_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, zero_sub, inner_neg_left] at h
  rw [closedGradientResolvent_apply]
  linarith

/-- The graph of the Friedrichs relation is recovered from its positive resolvent. -/
theorem closedGradientGraph_iff_resolvent
    (K : ClosedSubmodule ℝ (GradientHilbert H)) (u f : H) :
    ClosedGradientGraph K u f ↔ closedGradientResolvent K (f + u) = u := by
  constructor
  · rintro ⟨q, hq, hqu, hform⟩
    have hproj : K.toSubmodule.starProjection (gradientInjection (f + u)) = q := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hq
      intro r hr
      simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
        WithLp.sub_fst, WithLp.sub_snd, gradientInjection_apply,
        WithLp.toLp_fst, WithLp.toLp_snd, zero_sub, inner_neg_left, hqu,
        add_sub_cancel_right]
      linarith only [hform r hr]
    rw [closedGradientResolvent_apply, closedGradientResolventPair_apply, hproj, hqu]
  · intro h
    have hg := closedGradientResolvent_graph K (f + u)
    rwa [h, add_sub_cancel_right] at hg

theorem closedGradientResolvent_norm_le (K : ClosedSubmodule ℝ (GradientHilbert H)) :
    ‖closedGradientResolvent K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, closedGradientResolvent_apply]
  calc
    ‖(closedGradientResolventPair K f).fst‖ ≤ ‖closedGradientResolventPair K f‖ :=
      WithLp.norm_fst_le (α := H) (β := H) (p := 2) (closedGradientResolventPair K f)
    _ ≤ ‖gradientInjection f‖ := by
      rw [closedGradientResolventPair_apply]
      simpa only [one_mul] using K.toSubmodule.starProjection.le_of_opNorm_le_of_le
        K.toSubmodule.starProjection_norm_le (le_refl ‖gradientInjection f‖)
    _ = ‖f‖ := by
      rw [gradientInjection_apply, WithLp.norm_toLp_fst]

theorem closedGradientResolvent_isSymmetric
    (K : ClosedSubmodule ℝ (GradientHilbert H)) :
    (closedGradientResolvent K).toLinearMap.IsSymmetric := by
  intro f g
  have h := K.toSubmodule.inner_starProjection_left_eq_right
    (gradientInjection f) (gradientInjection g)
  rw [← closedGradientResolventPair_apply, ← closedGradientResolventPair_apply] at h
  simpa only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    gradientInjection_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    inner_zero_right, inner_zero_left, add_zero, closedGradientResolvent_apply,
    ContinuousLinearMap.coe_coe] using h

/-- The energy and `L²` norm of a positive resolvent are its pairing with the source. -/
theorem closedGradientResolvent_energy_identity
    (K : ClosedSubmodule ℝ (GradientHilbert H)) (f : H) :
    ⟪f, closedGradientResolvent K f⟫_ℝ = ‖closedGradientResolventPair K f‖ ^ 2 := by
  have h := K.toSubmodule.starProjection_inner_eq_zero (gradientInjection f)
    (closedGradientResolventPair K f) (closedGradientResolventPair_mem K f)
  rw [← closedGradientResolventPair_apply, inner_sub_left,
    real_inner_self_eq_norm_sq] at h
  rw [closedGradientResolvent_apply]
  simpa only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    gradientInjection_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    inner_zero_left, add_zero, sub_eq_zero] using h

/-- Monotone exhaustion of closed gradient spaces gives strong resolvent convergence. -/
theorem closedGradientResolvent_tendsto
    (K : ClosedSubmodule ℝ (GradientHilbert H))
    (Kₙ : ℕ → ClosedSubmodule ℝ (GradientHilbert H))
    (hmono : Monotone Kₙ)
    (hclosure : K.toSubmodule = (⨆ n : ℕ, (Kₙ n).toSubmodule).topologicalClosure)
    (f : H) :
    Tendsto (fun n => closedGradientResolvent (Kₙ n) f) atTop
      (𝓝 (closedGradientResolvent K f)) := by
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun n => (Kₙ n).toSubmodule) hmono (gradientInjection f)
  have hproj : (⨆ n : ℕ, (Kₙ n).toSubmodule).topologicalClosure.starProjection
      (gradientInjection f) = K.toSubmodule.starProjection (gradientInjection f) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact (congrArg (fun M : Submodule ℝ (GradientHilbert H) =>
        K.toSubmodule.starProjection (gradientInjection f) ∈ M) hclosure).mp
          (K.toSubmodule.starProjection_apply_mem _)
    · intro w hw
      exact K.toSubmodule.starProjection_inner_eq_zero (gradientInjection f) w
        ((congrArg (fun M : Submodule ℝ (GradientHilbert H) => w ∈ M) hclosure).mpr hw)
  rw [hproj] at ht
  have hf := ((WithLp.fstL 2 ℝ H H).continuous.tendsto _).comp ht
  simpa only [Function.comp_def, WithLp.fstL_apply, closedGradientResolvent_apply,
    closedGradientResolventPair_apply] using hf

end ContinuousFlexibility.Radial
