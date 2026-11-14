module

public import ContinuousFlexibility.Analysis.PeriodicScalarFlow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Joint parameter-angle Lipschitz bounds for periodic fields

Joint continuity of the actual state derivative on a compact parameter
set and one angular period gives a uniform derivative bound.  The mean
value theorem on the convex parameter-angle domain converts this into
the joint Lipschitz hypothesis used by parameter-dependent Gronwall.

An additional compact index set allows the same constant for every
time in a closed interval.  No differentiability in that index is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped NNReal Topology

variable {X P E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Global angular periodicity passes to the actual Fréchet derivative.
This also covers points where the actual derivative takes its default
zero value; no regularity is assumed outside the parameter domain. -/
theorem fderiv_periodic_snd
    {F : P × ℝ → E} {T : ℝ}
    (hperiod : ∀ p : P, Function.Periodic (fun θ => F (p, θ)) T)
    (p : P) :
    Function.Periodic (fun θ => fderiv ℝ F (p, θ)) T := by
  have htranslate : (fun x : P × ℝ => F (x + ((0 : P), T))) = F := by
    funext x
    rcases x with ⟨q, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using hperiod q θ
  intro θ
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := (p, θ)) ((0 : P), T)
  rw [htranslate] at hd
  simpa only [Prod.mk_add_mk, add_zero] using hd.symm

/-- A continuous periodic family of actual derivatives yields one joint
parameter-angle Lipschitz constant, uniform over a compact index set. -/
theorem exists_uniform_lipschitzOnWith_periodic_fderiv
    {I : Set X} {S : Set P} {F : X → P × ℝ → E} {T : ℝ}
    (hI : IsCompact I) (hS : IsCompact S) (hconv : Convex ℝ S)
    (hT : T ≠ 0)
    (hF : ∀ t ∈ I, ∀ x ∈ S ×ˢ univ, DifferentiableAt ℝ (F t) x)
    (hD : ContinuousOn
      (fun x : (X × P) × ℝ => fderiv ℝ (F x.1.1) (x.1.2, x.2))
      ((I ×ˢ S) ×ˢ univ))
    (hperiod : ∀ t ∈ I, ∀ p ∈ S,
      Function.Periodic (fun θ => fderiv ℝ (F t) (p, θ)) T) :
    ∃ K : ℝ≥0, ∀ t ∈ I, LipschitzOnWith K (F t) (S ×ˢ univ) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_bound_periodic_compact
    (hI.prod hS) hT hD (fun (x : X × P) hx => hperiod x.1 hx.1 x.2 hx.2)
  refine ⟨NNReal.mk M hM0, ?_⟩
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [dist_eq_norm, NNReal.coe_mk] using
    (hconv.prod (convex_univ : Convex ℝ (univ : Set ℝ))).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun (z : P × ℝ) hz => (hF t ht z hz).hasFDerivAt.hasFDerivWithinAt)
      (fun (z : P × ℝ) hz => hM (t, z.1) ⟨ht, hz.1⟩ z.2) hy hx

end ContinuousFlexibility.Analysis
