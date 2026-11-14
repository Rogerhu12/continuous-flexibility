module

public import ContinuousFlexibility.Analysis.CircleModelRealization
public import ContinuousFlexibility.Analysis.ProjectiveDifferential

/-!
# Nonlinear realization and limits in the actual circle model

Every weighted smooth circle field has a unique realization in the supplied
projective limit. Convergence and directional derivatives are tested in all
of its physical weighted norms. In particular, scalar pointwise derivative
identities are not substituted for convergence in the circle topology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Filter ContinuousFlexibility.Analysis
open scoped Topology

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

/-- The unique actual circle-space representative of a weighted field. -/
def circleRealize (hS : IsCircleModel T γ S) (f : ℕ → ℝ → ℝ)
    (hf : CircleMember T γ f) : S.Space :=
  Classical.choose (hS.2.2.2.2.1 f hf)

theorem circleRealize_decode (hS : IsCircleModel T γ S) (f : ℕ → ℝ → ℝ)
    (hf : CircleMember T γ f) :
    S.decode (circleRealize hS f hf) = f :=
  Classical.choose_spec (hS.2.2.2.2.1 f hf)

theorem circleRealize_unique (hS : IsCircleModel T γ S) (f : ℕ → ℝ → ℝ)
    (hf : CircleMember T γ f) (u : S.Space) (hu : S.decode u = f) :
    circleRealize hS f hf = u := by
  apply hS.2.2.2.2.2.1
  exact (circleRealize_decode hS f hf).trans hu.symm

/-- The projective topology is exactly convergence in every physical
circle norm of the difference. -/
theorem circle_tendsto_iff_norm (hS : IsCircleModel T γ S)
    {α : Type*} {l : Filter α} (u : α → S.Space) (v : S.Space) :
    Tendsto u l (𝓝 v) ↔
      ∀ s, Tendsto (fun a => circleNorm T γ s (S.decode (u a - v))) l (𝓝 0) := by
  have hn : ∀ w : S.Space, ∀ s, ‖w.val s‖ = circleNorm T γ s (S.decode w) :=
    hS.2.2.2.2.2.2.2
  have hsub (a : α) (s : ℕ) :
      (u a - v).val s = (u a).val s - v.val s := by
    simpa only [projectiveCoordinate_apply] using
      (projectiveCoordinate (fun s => S.level s) S.bond s).map_sub (u a) v
  rw [tendsto_projectiveLimit_iff]
  constructor
  · intro h s
    have hs := tendsto_iff_norm_sub_tendsto_zero.mp (h s)
    simpa only [← hn, hsub] using hs
  · intro h s
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [← hn, hsub] using h s

/-- A genuine circle-valued curve derivative is equivalent to vanishing
of every weighted norm of its decoded difference-quotient error. -/
theorem circle_hasProjectiveCurveDerivAt_iff (hS : IsCircleModel T γ S)
    (c : ℝ → S.Space) (dc : S.Space) (t : ℝ) :
    HasProjectiveCurveDerivAt c dc t ↔
      ∀ s, Tendsto (fun h : ℝ => circleNorm T γ s (fun m θ =>
        h⁻¹ * (S.decode (c (t + h)) m θ - S.decode (c t) m θ) -
          S.decode dc m θ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hdecode (h : ℝ) :
      S.decode (h⁻¹ • (c (t + h) - c t) - dc) =
        (fun m θ => h⁻¹ * (S.decode (c (t + h)) m θ - S.decode (c t) m θ) -
          S.decode dc m θ) := by
    ext m θ
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hlim := circle_tendsto_iff_norm hS (l := 𝓝[≠] (0 : ℝ))
    (fun h : ℝ => h⁻¹ • (c (t + h) - c t)) dc
  exact hlim.trans (by simp only [hdecode])

/-- The same criterion along a real affine line retains the full target
topology, including the infinite sum over physical components. -/
theorem circle_hasProjectiveLineDerivAt_iff (hS : IsCircleModel T γ S)
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → S.Space) (df : S.Space) (x v : E) :
    HasProjectiveLineDerivAt f df x v ↔
      ∀ s, Tendsto (fun h : ℝ => circleNorm T γ s (fun m θ =>
        h⁻¹ * (S.decode (f (x + h • v)) m θ - S.decode (f x) m θ) -
          S.decode df m θ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  simpa only [HasProjectiveLineDerivAt, zero_add, zero_smul, add_zero] using
    circle_hasProjectiveCurveDerivAt_iff hS (fun t : ℝ => f (x + t • v)) df 0

end ContinuousFlexibility.Statements
