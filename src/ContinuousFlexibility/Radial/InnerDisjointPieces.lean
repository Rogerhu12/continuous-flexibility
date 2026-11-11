import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Orthogonal assembly in the actual source measure

The functions on the disjoint open pieces are extended by zero and
summed in one ambient `L²` space. This applies to the physical radial
measure as well as to the model coordinate. The central scalar border
is placed in exactly one piece of a Hilbert product.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]

/-- Disjoint physical supports give actual `L²` orthogonality. -/
theorem innerL2_disjoint_inner_zero {s t : Set α} (hst : Disjoint s t)
    (f g : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0)
    (hg : ∀ᵐ x ∂μ, x ∉ t → g x = 0) : ⟪f, g⟫_ℝ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hf, hg] with x hfx hgx
  by_cases hx : x ∈ s
  · have hxt : x ∉ t := fun h => (Set.disjoint_left.mp hst) hx h
    rw [hgx hxt, inner_zero_right]
  · rw [hfx hx, inner_zero_left]

/-- A finite orthogonal sum has the sum of the squared local norms.
This identity avoids a loss proportional to the number of pieces. -/
theorem inner_orthogonal_sum_norm_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ι → H) (horth : ∀ i j, i ≠ j → ⟪f i, f j⟫_ℝ = 0) :
    ‖∑ i, f i‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq (f i)
  · intro j _ hji
    exact horth i j hji.symm
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem innerL2_disjoint_sum_norm_sq (s : ι → Set α)
    (hdis : Pairwise (Disjoint on s)) (f : ι → Lp ℝ 2 μ)
    (hsupport : ∀ i, ∀ᵐ x ∂μ, x ∉ s i → f i x = 0) :
    ‖∑ i, f i‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 :=
  inner_orthogonal_sum_norm_sq f (fun i j hij =>
    innerL2_disjoint_inner_zero (hdis hij) (f i) (f j) (hsupport i) (hsupport j))

/-- A central scalar is represented with the Hilbert norm. -/
abbrev InnerBorderL2 (μ : Measure α) := WithLp 2 (Lp ℝ 2 μ × ℝ)

theorem innerBorderL2_inner (f g : Lp ℝ 2 μ) (c d : ℝ) :
    ⟪(WithLp.toLp 2 (f, c) : InnerBorderL2 μ), WithLp.toLp 2 (g, d)⟫_ℝ =
      ⟪f, g⟫_ℝ + c * d := by
  rw [WithLp.prod_inner_apply]
  simp only [WithLp.ofLp_toLp, real_inner_eq_mul]
  ring

theorem innerBorderL2_norm_sq (f : Lp ℝ 2 μ) (c : ℝ) :
    ‖(WithLp.toLp 2 (f, c) : InnerBorderL2 μ)‖ ^ 2 = ‖f‖ ^ 2 + c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, innerBorderL2_inner, real_inner_self_eq_norm_sq]
  ring

/-- Only the distinguished central piece carries the scalar coordinate. -/
def innerBorderPiece [DecidableEq ι] (center : ι) (f : ι → Lp ℝ 2 μ)
    (c : ℝ) (i : ι) : InnerBorderL2 μ :=
  WithLp.toLp 2 (f i, if i = center then c else 0)

theorem innerBorderPiece_inner_zero [DecidableEq ι] (center : ι)
    (s : ι → Set α) (hdis : Pairwise (Disjoint on s))
    (f : ι → Lp ℝ 2 μ) (hsupport : ∀ i, ∀ᵐ x ∂μ, x ∉ s i → f i x = 0)
    (c : ℝ) {i j : ι} (hij : i ≠ j) :
    ⟪innerBorderPiece center f c i, innerBorderPiece center f c j⟫_ℝ = 0 := by
  rw [innerBorderPiece, innerBorderPiece, innerBorderL2_inner,
    innerL2_disjoint_inner_zero (hdis hij) (f i) (f j) (hsupport i) (hsupport j), zero_add]
  by_cases hi : i = center
  · have hj : j ≠ center := fun h => hij (hi.trans h.symm)
    rw [if_pos hi, if_neg hj, mul_zero]
  · rw [if_neg hi, zero_mul]

/-- The assembled scalar is counted once, while all local function
energies add orthogonally. This includes the unbordered case `c = 0`. -/
theorem innerBorderPiece_sum_norm_sq [DecidableEq ι] (center : ι)
    (s : ι → Set α) (hdis : Pairwise (Disjoint on s))
    (f : ι → Lp ℝ 2 μ) (hsupport : ∀ i, ∀ᵐ x ∂μ, x ∉ s i → f i x = 0) (c : ℝ) :
    ‖∑ i, innerBorderPiece center f c i‖ ^ 2 = (∑ i, ‖f i‖ ^ 2) + c ^ 2 := by
  rw [inner_orthogonal_sum_norm_sq _ (fun i j hij =>
    innerBorderPiece_inner_zero center s hdis f hsupport c hij)]
  simp only [innerBorderPiece, innerBorderL2_norm_sq, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single center]
  · simp only [if_pos rfl]
  · intro i _ hi
    simp only [if_neg hi, zero_pow (by decide : 2 ≠ 0)]
  · intro hc
    exact (hc (Finset.mem_univ center)).elim

end ContinuousFlexibility.Radial
