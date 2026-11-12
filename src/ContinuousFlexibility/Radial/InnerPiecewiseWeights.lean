import ContinuousFlexibility.Radial.InnerCoefficientWeights
import ContinuousFlexibility.Radial.InnerWeightL2

/-!
# Actual finite piecewise weights and coefficient loss

A finite disjoint family of measurable pieces carries the prescribed
local weight functions, and the weight is one elsewhere. In particular
the coefficient loss is an actual positive measurable function bounded
by one, with the required coefficient value on each physical piece.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real ContinuousFlexibility.Statements
open scoped BigOperators

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

def innerPiecewiseWeight (sets : ι → Set α) (w : ι → α → ℝ) (x : α) : ℝ :=
  1 + ∑ i, (sets i).indicator (fun y => w i y - 1) x

theorem innerPiecewiseWeight_measurable (sets : ι → Set α)
    (hs : ∀ i, MeasurableSet (sets i)) (w : ι → α → ℝ)
    (hw : ∀ i, Measurable (w i)) : Measurable (innerPiecewiseWeight sets w) := by
  apply measurable_const.add
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    ((hw i).sub measurable_const).indicator (hs i))

theorem innerPiecewiseWeight_on_piece (sets : ι → Set α)
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (w : ι → α → ℝ) {i : ι} {x : α} (hx : x ∈ sets i) :
    innerPiecewiseWeight sets w x = w i x := by
  classical
  unfold innerPiecewiseWeight
  rw [Finset.sum_eq_single i]
  · rw [indicator_of_mem hx]
    ring
  · intro k _ hki
    exact indicator_of_notMem (fun hk => (Set.disjoint_left.mp (hdis hki)) hk hx) _
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem innerPiecewiseWeight_outside (sets : ι → Set α) (w : ι → α → ℝ)
    {x : α} (hx : x ∉ ⋃ i, sets i) : innerPiecewiseWeight sets w x = 1 := by
  unfold innerPiecewiseWeight
  have hz : ∀ i, (sets i).indicator (fun y => w i y - 1) x = 0 := fun i =>
    indicator_of_notMem (fun h => hx (mem_iUnion.mpr ⟨i, h⟩)) _
  simp only [hz, Finset.sum_const_zero, add_zero]

theorem innerPiecewiseWeight_pos (sets : ι → Set α)
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (w : ι → α → ℝ) (hw : ∀ i x, x ∈ sets i → 0 < w i x) (x : α) :
    0 < innerPiecewiseWeight sets w x := by
  by_cases hx : x ∈ ⋃ i, sets i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [innerPiecewiseWeight_on_piece sets hdis w hi]
    exact hw i x hi
  · rw [innerPiecewiseWeight_outside sets w hx]
    exact zero_lt_one

theorem innerPiecewiseWeight_bound (sets : ι → Set α)
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (w : ι → α → ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hw : ∀ i x, x ∈ sets i → |w i x| ≤ C) (x : α) :
    |innerPiecewiseWeight sets w x| ≤ C := by
  by_cases hx : x ∈ ⋃ i, sets i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [innerPiecewiseWeight_on_piece sets hdis w hi]
    exact hw i x hi
  · rw [innerPiecewiseWeight_outside sets w hx, abs_one]
    exact hC

theorem innerPiecewiseWeight_inv_bound (sets : ι → Set α)
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (w : ι → α → ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hw : ∀ i x, x ∈ sets i → |(w i x)⁻¹| ≤ C) (x : α) :
    |(innerPiecewiseWeight sets w x)⁻¹| ≤ C := by
  by_cases hx : x ∈ ⋃ i, sets i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [innerPiecewiseWeight_on_piece sets hdis w hi]
    exact hw i x hi
  · rw [innerPiecewiseWeight_outside sets w hx, inv_one, abs_one]
    exact hC

/-- The coefficient loss is one on the finite middle part (index N). -/
def innerPiecewiseCoefficientLoss (sets : ι → Set α) (index : ι → ℕ)
    (N : ℕ) (ℓ : ℝ) : α → ℝ :=
  innerPiecewiseWeight sets (fun i _ => innerCoefficientLoss N ℓ (index i))

theorem innerPiecewiseCoefficientLoss_measurable (sets : ι → Set α)
    (hs : ∀ i, MeasurableSet (sets i)) (index : ι → ℕ) (N : ℕ) (ℓ : ℝ) :
    Measurable (innerPiecewiseCoefficientLoss sets index N ℓ) :=
  innerPiecewiseWeight_measurable sets hs _ (fun _ => measurable_const)

theorem innerPiecewiseCoefficientLoss_pos (sets : ι → Set α)
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (index : ι → ℕ) (N : ℕ) (ℓ : ℝ) (x : α) :
    0 < innerPiecewiseCoefficientLoss sets index N ℓ x :=
  innerPiecewiseWeight_pos sets hdis _ (fun i _ _ => innerCoefficientLoss_pos N ℓ (index i)) x

theorem innerPiecewiseCoefficientLoss_le_one (sets : ι → Set α)
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (index : ι → ℕ) {N : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hindex : ∀ i, N ≤ index i) (x : α) :
    |innerPiecewiseCoefficientLoss sets index N ℓ x| ≤ 1 := by
  apply innerPiecewiseWeight_bound sets hdis _ le_rfl
  intro i _ _
  rw [abs_of_pos (innerCoefficientLoss_pos N ℓ (index i))]
  exact innerCoefficientLoss_le_one hℓ (hindex i)

theorem norm_innerPiecewiseCoefficientLossMultiplier_le_one
    (μ : Measure α) (sets : ι → Set α) (hs : ∀ i, MeasurableSet (sets i))
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (index : ι → ℕ) {N : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hindex : ∀ i, N ≤ index i) :
    ‖innerWeightMultiplier μ (innerPiecewiseCoefficientLoss sets index N ℓ)
      (innerPiecewiseCoefficientLoss_measurable sets hs index N ℓ) 1
      (innerPiecewiseCoefficientLoss_le_one sets hdis index hℓ hindex)‖ ≤ 1 :=
  norm_innerWeightMultiplier_le μ _ _ 1 zero_le_one _

end ContinuousFlexibility.Radial
