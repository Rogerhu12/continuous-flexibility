module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Square-summable orthogonal vectors

The one-dimensional spans turn a pairwise orthogonal family of vectors,
including zero vectors, into mathlib's orthogonal family of subspaces.
This supplies strong summability and the exact squared norm of the sum.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter
open scoped BigOperators Topology

theorem r11b_orthogonal_series_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (v : ℕ → E) (horth : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hsq : Summable (fun i => ‖v i‖ ^ 2)) :
    Summable v ∧ ‖∑' i, v i‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  let G (i : ℕ) : Submodule ℝ E := Submodule.span ℝ {v i}
  let V (i : ℕ) : G i →ₗᵢ[ℝ] E := (G i).subtypeₗᵢ
  have hV : OrthogonalFamily ℝ (fun i => G i) V := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
    change inner ℝ (x : E) (y : E) = 0
    rw [← ha, ← hb]
    simp only [real_inner_smul_left, real_inner_smul_right, horth hij, mul_zero]
  let f (i : ℕ) : G i := ⟨v i, Submodule.subset_span (by simp)⟩
  have hs : Summable v := (hV.summable_iff_norm_sq_summable f).mpr hsq
  refine ⟨hs, ?_⟩
  have hnorm (n : ℕ) :
      ‖∑ i ∈ Finset.range n, v i‖ ^ 2 = ∑ i ∈ Finset.range n, ‖v i‖ ^ 2 :=
    hV.norm_sum f (Finset.range n)
  have hleft : Tendsto (fun n => ‖∑ i ∈ Finset.range n, v i‖ ^ 2) atTop
      (𝓝 (‖∑' i, v i‖ ^ 2)) :=
    hs.hasSum.tendsto_sum_nat.norm.pow 2
  have hright : Tendsto (fun n => ‖∑ i ∈ Finset.range n, v i‖ ^ 2) atTop
      (𝓝 (∑' i, ‖v i‖ ^ 2)) := by
    simp_rw [hnorm]
    exact hsq.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hleft hright

end ContinuousFlexibility.Radial
