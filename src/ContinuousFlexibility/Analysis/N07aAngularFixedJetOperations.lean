module

public import ContinuousFlexibility.Analysis.N07aAngularFixedJetEnvelope

/-!
# Finite differential operations retain the actual material envelope

These operations apply to the displayed spatial fields at a fixed state.
In particular a physical derivative shifts only the finite jet order; it
does not spend any of the sampled height factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

namespace N07aAngularFixedJetEnvelope

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem add
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set E} {w : ℕ → ℝ} {f g : ℕ → E → F}
    (hW : ∀ m, IsOpen (W m))
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (W m))
    (hgs : ∀ m, ContDiffOn ℝ ∞ (g m) (W m))
    (hf : N07aAngularFixedJetEnvelope T K W w f)
    (hg : N07aAngularFixedJetEnvelope T K W w g) :
    N07aAngularFixedJetEnvelope T K W w (fun m x => f m x + g m x) := by
  intro n
  obtain ⟨a, ha, ha0, hab⟩ := hf n
  obtain ⟨b, hb, hb0, hbb⟩ := hg n
  refine ⟨fun m => a m + b m, ha.add hb,
    fun m => add_nonneg (ha0 m) (hb0 m), fun m x hx => ?_⟩
  have he : (fun x => f m x + g m x) = f m + g m := by
    funext y
    exact (Pi.add_apply _ _ _).symm
  have hd : iteratedFDeriv ℝ n (f m + g m) x =
      iteratedFDeriv ℝ n (f m) x + iteratedFDeriv ℝ n (g m) x :=
    iteratedFDeriv_add_apply
      (((hfs m).contDiffAt ((hW m).mem_nhds hx)).of_le (by simp))
      (((hgs m).contDiffAt ((hW m).mem_nhds hx)).of_le (by simp))
  exact (congrArg (fun h : E → F => ‖iteratedFDeriv ℝ n h x‖) he).le.trans
    ((congrArg norm hd).le.trans ((norm_add_le _ _).trans
      ((add_le_add (hab m x hx) (hbb m x hx)).trans_eq
        (add_mul (a m) (b m) (w m)).symm)))

theorem directional
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set E} {w : ℕ → ℝ} {f : ℕ → E → F}
    (hW : ∀ m, IsOpen (W m))
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (W m))
    (hf : N07aAngularFixedJetEnvelope T K W w f) (v : E) :
    N07aAngularFixedJetEnvelope T K W w
      (fun m x => fderiv ℝ (f m) x v) := by
  intro n
  obtain ⟨e, he, he0, heb⟩ := hf (n + 1)
  refine ⟨fun m => ‖v‖ * e m,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT ‖v‖) he,
    fun m => mul_nonneg (norm_nonneg v) (he0 m), fun m x hx => ?_⟩
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ (f m)) x :=
    ((hfs m).contDiffAt ((hW m).mem_nhds hx)).fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const (c := v) (n := n) hd (by simp)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (heb m x hx) (norm_nonneg v)).trans_eq
    (mul_assoc ‖v‖ (e m) (w m)).symm)

theorem of_uniform_jets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set E} {f : ℕ → E → F}
    (hf : ∀ n, ∃ A : ℝ, 0 ≤ A ∧
      ∀ m x, x ∈ W m → ‖iteratedFDeriv ℝ n (f m) x‖ ≤ A) :
    N07aAngularFixedJetEnvelope T K W (fun _ => 1) f := by
  intro n
  obtain ⟨A, hA, hAb⟩ := hf n
  exact ⟨fun _ => A, N07aSampleSubpower.const hD hT A, fun _ => hA,
    fun m x hx => by simpa only [mul_one] using hAb m x hx⟩

end N07aAngularFixedJetEnvelope

end ContinuousFlexibility.Analysis
