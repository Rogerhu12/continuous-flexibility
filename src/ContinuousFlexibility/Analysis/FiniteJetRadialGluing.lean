import ContinuousFlexibility.Analysis.FiniteJetGluing
import ContinuousFlexibility.Scalar.Coordinates

/-!
# Finite matching at an actual radial interface

This adapter applies the full-jet gluing theorem to a radial circle.
The left and right functions need ordinary regularity only at the
points of their own closed half-strip. It applies to a closed negative
root extension and the adjacent positive Taylor construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual finite-order matching on the circle suffices on the open
strip; no common infinite-order collar is needed. -/
theorem contDiffOn_radial_piecewise_of_matching_full_jets
    (n : ℕ) {a b c : ℝ} {f g : PolarPoint → F}
    (hf : ∀ p : PolarPoint, a < p.1 → p.1 ≤ c → p.1 < b → ContDiffAt ℝ n f p)
    (hg : ∀ p : PolarPoint, a < p.1 → c ≤ p.1 → p.1 < b → ContDiffAt ℝ n g p)
    (hmatch : ∀ θ : ℝ, ∀ k : ℕ, k ≤ n →
      iteratedFDeriv ℝ k f (c, θ) = iteratedFDeriv ℝ k g (c, θ)) :
    ContDiffOn ℝ n (fun p : PolarPoint => if p.1 ≤ c then f p else g p)
      (Ioo a b ×ˢ (univ : Set ℝ)) := by
  classical
  let U : Set PolarPoint := Ioo a b ×ˢ univ
  let s : Set PolarPoint := {p | p.1 ≤ c}
  let t : Set PolarPoint := {p | c ≤ p.1}
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hs : IsClosed s := isClosed_le continuous_fst continuous_const
  have ht : IsClosed t := isClosed_le continuous_const continuous_fst
  have hleft : closure s ⊆ s := by
    intro p hp
    rw [hs.closure_eq] at hp
    exact hp
  have hright : closure sᶜ ⊆ t :=
    closure_minimal (by
      intro p hp
      change ¬ p.1 ≤ c at hp
      change c ≤ p.1
      exact le_of_lt (lt_of_not_ge hp)) ht
  have hregular : ContDiffOn ℝ n (s.piecewise f g) U := by
    apply contDiffOn_nat_piecewise_of_matching_full_jets n hU
    · intro p hp
      exact hf p hp.1.1.1 (hleft hp.2) hp.1.1.2
    · intro p hp
      exact hg p hp.1.1.1 (hright hp.2) hp.1.1.2
    · rintro ⟨x, θ⟩ hp k hk
      have hfront := hp.2
      rw [frontier_eq_closure_inter_closure] at hfront
      have hx : x = c := le_antisymm (hleft hfront.1) (hright hfront.2)
      subst x
      exact hmatch θ k hk
  have he : s.piecewise f g = (fun p : PolarPoint => if p.1 ≤ c then f p else g p) := by
    funext p
    by_cases hp : p.1 ≤ c
    · rw [piecewise_eq_of_mem s f g hp, if_pos hp]
    · rw [piecewise_eq_of_notMem s f g hp, if_neg hp]
  rw [he] at hregular
  exact hregular

/-- A globally stored field which has the actual local piecewise values
inherits the finite regularity at every point of this strip. -/
theorem contDiffAt_of_local_radial_piecewise_matching_full_jets
    (n : ℕ) {a b c : ℝ} {f g H : PolarPoint → F}
    (hf : ∀ p : PolarPoint, a < p.1 → p.1 ≤ c → p.1 < b → ContDiffAt ℝ n f p)
    (hg : ∀ p : PolarPoint, a < p.1 → c ≤ p.1 → p.1 < b → ContDiffAt ℝ n g p)
    (hmatch : ∀ θ : ℝ, ∀ k : ℕ, k ≤ n →
      iteratedFDeriv ℝ k f (c, θ) = iteratedFDeriv ℝ k g (c, θ))
    (hH : ∀ p : PolarPoint, p.1 ∈ Ioo a b →
      H p = if p.1 ≤ c then f p else g p)
    {p : PolarPoint} (hp : p.1 ∈ Ioo a b) : ContDiffAt ℝ n H p := by
  have hU : IsOpen (Ioo a b ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hpU : p ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
  have he : H =ᶠ[𝓝 p] (fun q : PolarPoint => if q.1 ≤ c then f q else g q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact hH q hq.1
  exact ((contDiffOn_radial_piecewise_of_matching_full_jets n hf hg hmatch).contDiffAt
    (hU.mem_nhds hpU)).congr_of_eventuallyEq he

end ContinuousFlexibility.Analysis
