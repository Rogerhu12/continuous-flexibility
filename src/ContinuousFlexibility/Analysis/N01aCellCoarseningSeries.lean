import ContinuousFlexibility.Analysis.N01aCellCoarsening
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Weighted square sums under finite-fiber coarsening

Weights are constant on each fiber. The actual coarse square integrals are
summable exactly when the fine weighted integrals are summable, and their
sums are comparable with constants one and the original overlap number.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators

variable {ι κ Ω : Type*}

theorem n01a_tsum_fiber_eq_sum (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) (f : ι → ℝ) (j : κ) :
    (∑' i : {i | σ i = j}, f i) = ∑ i ∈ n01aCoarseningFiber σ hσ j, f i := by
  have ht := Finset.tsum_subtype' (hσ j).toFinset f
  rw [(hσ j).coe_toFinset] at ht
  exact ht

/-- Regrouping a nonnegative real series along finite fibers preserves summability. -/
theorem n01a_summable_fiber_sum_iff (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    Summable (fun j => ∑ i ∈ n01aCoarseningFiber σ hσ j, f i) ↔ Summable f := by
  have hpart : ∀ i : ι, ∃! j : κ, i ∈ ({i' | σ i' = j} : Set ι) := by
    intro i
    refine ⟨σ i, rfl, ?_⟩
    intro j hj
    exact hj.symm
  have hfinite (j : κ) : Summable (fun i : {i | σ i = j} => f i) := by
    letI : Finite {i | σ i = j} := (hσ j).to_subtype
    exact Summable.of_finite
  have he := summable_partition hf hpart
  constructor
  · intro hs
    apply he.mpr
    refine ⟨hfinite, ?_⟩
    simpa only [n01a_tsum_fiber_eq_sum σ hσ f] using hs
  · intro hs
    simpa only [n01a_tsum_fiber_eq_sum σ hσ f] using (he.mp hs).2

theorem n01a_tsum_coarsening_fiber_sum (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) {f : ι → ℝ} (hf : Summable f) :
    (∑' j, ∑ i ∈ n01aCoarseningFiber σ hσ j, f i) = ∑' i, f i := by
  have h : HasSum (fun j => ∑' i : {i | σ i = j}, f i) (∑' i, f i) :=
    hf.hasSum.tsum_fiberwise σ
  have h' : HasSum (fun j => ∑ i ∈ n01aCoarseningFiber σ hσ j, f i)
      (∑' i, f i) := by
    simpa only [n01a_tsum_fiber_eq_sum σ hσ f] using h
  exact h'.tsum_eq

theorem n01aCoarseningFiber_sum_mul (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) (Λ : κ → ℝ) (f : ι → ℝ) (j : κ) :
    (∑ i ∈ n01aCoarseningFiber σ hσ j, Λ (σ i) * f i) =
      Λ j * ∑ i ∈ n01aCoarseningFiber σ hσ j, f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(mem_n01aCoarseningFiber σ hσ i j).mp hi]

section Measure

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- The two inequalities for the actual weighted integral of one coarse cell. -/
theorem n01aCoarseLocalizer_weighted_integral_bounds (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) {χ : ι → Ω → ℝ} {F : Ω → ℝ}
    (hχnonneg : ∀ i x, 0 ≤ χ i x) (hχ : ∀ i, AEMeasurable (χ i) μ)
    (hF : AEMeasurable (fun x => F x ^ 2) μ)
    (hI : ∀ i, Integrable (fun x => (χ i x * F x) ^ 2) μ)
    (B : ℕ) (hB : ∀ x, {i | χ i x ≠ 0}.Finite ∧ {i | χ i x ≠ 0}.ncard ≤ B)
    (Λ : κ → ℝ) (hΛ : ∀ j, 0 ≤ Λ j) (j : κ) :
    (∑ i ∈ n01aCoarseningFiber σ hσ j, Λ (σ i) * n01aLocalSquare μ χ F i) ≤
      Λ j * n01aLocalSquare μ (n01aCoarseLocalizer σ hσ χ) F j ∧
    Λ j * n01aLocalSquare μ (n01aCoarseLocalizer σ hσ χ) F j ≤
      (B : ℝ) * ∑ i ∈ n01aCoarseningFiber σ hσ j,
        Λ (σ i) * n01aLocalSquare μ χ F i := by
  have h := n01aCoarseLocalizer_integral_bounds μ σ hσ hχnonneg hχ hF hI B hB j
  simp only [n01aCoarseningFiber_sum_mul σ hσ Λ (n01aLocalSquare μ χ F) j]
  constructor
  · exact mul_le_mul_of_nonneg_left h.1 (hΛ j)
  · calc
      _ ≤ Λ j * ((B : ℝ) *
          ∑ i ∈ n01aCoarseningFiber σ hσ j, n01aLocalSquare μ χ F i) :=
        mul_le_mul_of_nonneg_left h.2 (hΛ j)
      _ = _ := by ring

/-- Summability is preserved in both directions for every nonnegative fiber weight. -/
theorem n01aCoarseLocalizer_summable_iff (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) {χ : ι → Ω → ℝ} {F : Ω → ℝ}
    (hχnonneg : ∀ i x, 0 ≤ χ i x) (hχ : ∀ i, AEMeasurable (χ i) μ)
    (hF : AEMeasurable (fun x => F x ^ 2) μ)
    (hI : ∀ i, Integrable (fun x => (χ i x * F x) ^ 2) μ)
    (B : ℕ) (hB : ∀ x, {i | χ i x ≠ 0}.Finite ∧ {i | χ i x ≠ 0}.ncard ≤ B)
    (Λ : κ → ℝ) (hΛ : ∀ j, 0 ≤ Λ j) :
    Summable (fun j => Λ j * n01aLocalSquare μ (n01aCoarseLocalizer σ hσ χ) F j) ↔
      Summable (fun i => Λ (σ i) * n01aLocalSquare μ χ F i) := by
  have hn (i : ι) : 0 ≤ Λ (σ i) * n01aLocalSquare μ χ F i :=
    mul_nonneg (hΛ (σ i)) (n01aLocalSquare_nonneg μ χ F i)
  have hg (j : κ) :
      0 ≤ Λ j * n01aLocalSquare μ (n01aCoarseLocalizer σ hσ χ) F j :=
    mul_nonneg (hΛ j) (n01aLocalSquare_nonneg μ _ F j)
  have hb := n01aCoarseLocalizer_weighted_integral_bounds
    μ σ hσ hχnonneg hχ hF hI B hB Λ hΛ
  have he := n01a_summable_fiber_sum_iff σ hσ
    (fun i => Λ (σ i) * n01aLocalSquare μ χ F i) hn
  constructor
  · intro hs
    exact he.mp (Summable.of_nonneg_of_le
      (fun j => Finset.sum_nonneg fun i _ => hn i) (fun j => (hb j).1) hs)
  · intro hs
    exact Summable.of_nonneg_of_le hg (fun j => (hb j).2)
      ((he.mpr hs).mul_left (B : ℝ))

/-- The complete weighted sums satisfy the same one-sided constants as each fiber. -/
theorem n01aCoarseLocalizer_tsum_bounds (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) {χ : ι → Ω → ℝ} {F : Ω → ℝ}
    (hχnonneg : ∀ i x, 0 ≤ χ i x) (hχ : ∀ i, AEMeasurable (χ i) μ)
    (hF : AEMeasurable (fun x => F x ^ 2) μ)
    (hI : ∀ i, Integrable (fun x => (χ i x * F x) ^ 2) μ)
    (B : ℕ) (hB : ∀ x, {i | χ i x ≠ 0}.Finite ∧ {i | χ i x ≠ 0}.ncard ≤ B)
    (Λ : κ → ℝ) (hΛ : ∀ j, 0 ≤ Λ j)
    (hs : Summable (fun i => Λ (σ i) * n01aLocalSquare μ χ F i)) :
    (∑' i, Λ (σ i) * n01aLocalSquare μ χ F i) ≤
      ∑' j, Λ j * n01aLocalSquare μ (n01aCoarseLocalizer σ hσ χ) F j ∧
    (∑' j, Λ j * n01aLocalSquare μ (n01aCoarseLocalizer σ hσ χ) F j) ≤
      (B : ℝ) * ∑' i, Λ (σ i) * n01aLocalSquare μ χ F i := by
  have hgroup := (n01a_summable_fiber_sum_iff σ hσ
    (fun i => Λ (σ i) * n01aLocalSquare μ χ F i)
    (fun i => mul_nonneg (hΛ (σ i)) (n01aLocalSquare_nonneg μ χ F i))).mpr hs
  have hc := (n01aCoarseLocalizer_summable_iff
    μ σ hσ hχnonneg hχ hF hI B hB Λ hΛ).mpr hs
  have hb := n01aCoarseLocalizer_weighted_integral_bounds
    μ σ hσ hχnonneg hχ hF hI B hB Λ hΛ
  have heq := n01a_tsum_coarsening_fiber_sum σ hσ hs
  constructor
  · calc
      _ = ∑' j, ∑ i ∈ n01aCoarseningFiber σ hσ j,
          Λ (σ i) * n01aLocalSquare μ χ F i := heq.symm
      _ ≤ _ := hgroup.tsum_le_tsum (fun j => (hb j).1) hc
  · calc
      _ ≤ ∑' j, (B : ℝ) * ∑ i ∈ n01aCoarseningFiber σ hσ j,
          Λ (σ i) * n01aLocalSquare μ χ F i :=
        hc.tsum_le_tsum (fun j => (hb j).2) (hgroup.mul_left (B : ℝ))
      _ = _ := by rw [tsum_mul_left, heq]

end Measure

end ContinuousFlexibility.Statements
