import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Ordinary jets on one angular period

Periodicity transports all actual ordinary jets. A degree-one lift
transports its positive-order jets; its unbounded zeroth-order angle
is never part of this estimate. Only smoothness at the evaluation
points is used for the lift statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem iteratedFDeriv_snd_periodic_of_periodic
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : PolarPoint → Y} {T : ℝ}
    (hperiod : ∀ r θ, f (r, θ + T) = f (r, θ)) (n : ℕ) (r : ℝ) :
    Function.Periodic (fun θ => iteratedFDeriv ℝ n f (r, θ)) T := by
  have he : (fun q : PolarPoint => f ((0, T) + q)) = f := by
    funext q
    rcases q with ⟨x, θ⟩
    simpa only [Prod.mk_add_mk, zero_add, add_comm T θ] using hperiod x θ
  intro θ
  have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) n (0, T) (r, θ)
  rw [he] at ht
  simpa only [Prod.mk_add_mk, zero_add, add_comm T θ] using ht.symm

theorem iteratedFDeriv_snd_periodic_of_lift
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : PolarPoint → Y} {T r : ℝ} {v : Y}
    (hperiod : ∀ x θ, f (x, θ + T) = f (x, θ) + v)
    (hf : ∀ θ, ContDiffAt ℝ ∞ f (r, θ)) {n : ℕ} (hn : 1 ≤ n) :
    Function.Periodic (fun θ => iteratedFDeriv ℝ n f (r, θ)) T := by
  have he : (fun q : PolarPoint => f ((0, T) + q)) = f + (fun _ => v) := by
    funext q
    rcases q with ⟨x, θ⟩
    simpa only [Prod.mk_add_mk, zero_add, add_comm T θ, Pi.add_apply] using hperiod x θ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro θ
  have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) (k + 1) (0, T) (r, θ)
  rw [he, iteratedFDeriv_add_apply
    ((hf θ).of_le (by simp : ((k + 1 : ℕ) : ℕ∞ω) ≤ ∞)) contDiffAt_const] at ht
  simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, add_zero,
    Prod.mk_add_mk, zero_add, add_comm T θ] using ht.symm

theorem norm_iteratedFDeriv_le_of_snd_periodic
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : PolarPoint → Y} {r M : ℝ} (n : ℕ)
    (hperiod : Function.Periodic (fun θ => iteratedFDeriv ℝ n f (r, θ)) Real.pi)
    (hbound : ∀ θ ∈ Icc (-Real.pi) Real.pi, ‖iteratedFDeriv ℝ n f (r, θ)‖ ≤ M)
    (θ : ℝ) : ‖iteratedFDeriv ℝ n f (r, θ)‖ ≤ M := by
  obtain ⟨t, ht, he⟩ := hperiod.exists_mem_Ico₀ Real.pi_pos θ
  change iteratedFDeriv ℝ n f (r, θ) = iteratedFDeriv ℝ n f (r, t) at he
  rw [he]
  exact hbound t ⟨(neg_nonpos.mpr Real.pi_pos.le).trans ht.1, ht.2.le⟩

end ContinuousFlexibility.Analysis
