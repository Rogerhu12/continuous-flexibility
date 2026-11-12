import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Actual square integrals under finite-fiber coarsening

Nonnegative localizers can be merged by summing each finite fiber. The
resulting square integral lies between the sum of the original square
integrals and the overlap number times that sum. Only measurability of the
square of the field is used; measurability of its sign is not required.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators

variable {ι κ Ω : Type*}

/-- The finite fiber used to merge a family of localizers. -/
def n01aCoarseningFiber (σ : ι → κ) (hσ : ∀ j, {i | σ i = j}.Finite)
    (j : κ) : Finset ι := (hσ j).toFinset

@[simp] theorem mem_n01aCoarseningFiber (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) (i : ι) (j : κ) :
    i ∈ n01aCoarseningFiber σ hσ j ↔ σ i = j :=
  (hσ j).mem_toFinset

/-- The actual coarse localizer is the sum of its fine localizers. -/
def n01aCoarseLocalizer (σ : ι → κ) (hσ : ∀ j, {i | σ i = j}.Finite)
    (χ : ι → Ω → ℝ) (j : κ) (x : Ω) : ℝ :=
  ∑ i ∈ n01aCoarseningFiber σ hσ j, χ i x

theorem n01aCoarseLocalizer_nonneg (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) (χ : ι → Ω → ℝ)
    (hχ : ∀ i x, 0 ≤ χ i x) (j : κ) (x : Ω) :
    0 ≤ n01aCoarseLocalizer σ hσ χ j x :=
  Finset.sum_nonneg fun i _ => hχ i x

theorem n01a_sum_localizer_squares_le (s : Finset ι) (χ : ι → ℝ)
    (hχ : ∀ i, 0 ≤ χ i) (a : ℝ) :
    (∑ i ∈ s, (χ i * a) ^ 2) ≤ ((∑ i ∈ s, χ i) * a) ^ 2 := by
  have h := mul_le_mul_of_nonneg_right
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := s) (fun i _ => hχ i)) (sq_nonneg a)
  simp only [mul_pow]
  simpa only [Finset.sum_mul] using h

theorem n01a_square_sum_localizer_le_card (s : Finset ι) (χ : ι → ℝ) (a : ℝ) :
    ((∑ i ∈ s, χ i) * a) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (χ i * a) ^ 2 := by
  have h := mul_le_mul_of_nonneg_right
    (sq_sum_le_card_mul_sum_sq (s := s) (f := χ)) (sq_nonneg a)
  simp only [mul_pow]
  simpa only [mul_assoc, Finset.sum_mul] using h

/-- The number of active fine localizers, rather than the fiber size, is the
constant in the square estimate. -/
theorem n01a_square_sum_localizer_le_overlap (s : Finset ι) (χ : ι → ℝ)
    (B : ℕ) (hfin : {i | χ i ≠ 0}.Finite) (hB : {i | χ i ≠ 0}.ncard ≤ B)
    (a : ℝ) :
    ((∑ i ∈ s, χ i) * a) ^ 2 ≤ (B : ℝ) * ∑ i ∈ s, (χ i * a) ^ 2 := by
  classical
  let t : Finset ι := s.filter (fun i => χ i ≠ 0)
  have hsub : t ⊆ hfin.toFinset := by
    intro i hi
    exact hfin.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
  have hcard : t.card ≤ B :=
    (Finset.card_le_card hsub).trans (by
      simpa only [← Set.ncard_eq_toFinset_card] using hB)
  have hsum : (∑ i ∈ t, χ i) = ∑ i ∈ s, χ i :=
    Finset.sum_filter_ne_zero s
  have hsq : (∑ i ∈ t, (χ i * a) ^ 2) = ∑ i ∈ s, (χ i * a) ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hit
    have hz : χ i = 0 := by
      by_contra hn
      exact hit (Finset.mem_filter.mpr ⟨hi, hn⟩)
    simp only [hz, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  calc
    _ = ((∑ i ∈ t, χ i) * a) ^ 2 := by rw [hsum]
    _ ≤ (t.card : ℝ) * ∑ i ∈ t, (χ i * a) ^ 2 :=
      n01a_square_sum_localizer_le_card t χ a
    _ ≤ (B : ℝ) * ∑ i ∈ t, (χ i * a) ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [hsq]

theorem n01a_fine_square_le_coarse_square (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) (χ : ι → Ω → ℝ)
    (hχ : ∀ i x, 0 ≤ χ i x) (i : ι) (x : Ω) (a : ℝ) :
    (χ i x * a) ^ 2 ≤ (n01aCoarseLocalizer σ hσ χ (σ i) x * a) ^ 2 := by
  classical
  apply le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (χ j x * a))
    ((mem_n01aCoarseningFiber σ hσ i (σ i)).mpr rfl))
  exact n01a_sum_localizer_squares_le _ (fun i => χ i x) (fun i => hχ i x) a

section Measure

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- The actual localized square integral, with no regularity encoded in its definition. -/
def n01aLocalSquare (χ : ι → Ω → ℝ) (F : Ω → ℝ) (i : ι) : ℝ :=
  ∫ x, (χ i x * F x) ^ 2 ∂μ

theorem n01aLocalSquare_nonneg (χ : ι → Ω → ℝ) (F : Ω → ℝ) (i : ι) :
    0 ≤ n01aLocalSquare μ χ F i := integral_nonneg fun _ => sq_nonneg _

theorem n01a_localized_square_aemeasurable {χ F : Ω → ℝ}
    (hχ : AEMeasurable χ μ) (hF : AEMeasurable (fun x => F x ^ 2) μ) :
    AEMeasurable (fun x => (χ x * F x) ^ 2) μ := by
  have he : ((fun x => χ x ^ 2) * (fun x => F x ^ 2) : Ω → ℝ) =
      (fun x => χ x ^ 2 * F x ^ 2) := by
    funext x
    simp only [Pi.mul_apply]
  have hm := (hχ.pow_const (2 : ℕ)).mul hF
  rw [he] at hm
  simpa only [mul_pow] using hm

theorem n01aCoarseLocalizer_aemeasurable (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) {χ : ι → Ω → ℝ}
    (hχ : ∀ i, AEMeasurable (χ i) μ) (j : κ) :
    AEMeasurable (n01aCoarseLocalizer σ hσ χ j) μ :=
  Finset.aemeasurable_fun_sum _ (fun i _ => hχ i)

/-- Finite coarsening preserves integrability of every localized square. -/
theorem n01aCoarseLocalizer_square_integrable (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) {χ : ι → Ω → ℝ} {F : Ω → ℝ}
    (hχ : ∀ i, AEMeasurable (χ i) μ)
    (hF : AEMeasurable (fun x => F x ^ 2) μ)
    (hI : ∀ i, Integrable (fun x => (χ i x * F x) ^ 2) μ) (j : κ) :
    Integrable (fun x => (n01aCoarseLocalizer σ hσ χ j x * F x) ^ 2) μ := by
  have hsum := integrable_finsetSum (n01aCoarseningFiber σ hσ j) (fun i _ => hI i)
  refine (hsum.const_mul ((n01aCoarseningFiber σ hσ j).card : ℝ)).mono_nonneg
    (n01a_localized_square_aemeasurable μ
      (n01aCoarseLocalizer_aemeasurable μ σ hσ hχ j) hF).aestronglyMeasurable
    (Eventually.of_forall fun _ => sq_nonneg _) ?_
  exact Eventually.of_forall fun x => n01a_square_sum_localizer_le_card
    (n01aCoarseningFiber σ hσ j) (fun i => χ i x) (F x)

/-- Nonnegative localizers also permit recovering each fine square from its coarse square. -/
theorem n01aCoarseLocalizer_integrable_iff (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) {χ : ι → Ω → ℝ} {F : Ω → ℝ}
    (hχnonneg : ∀ i x, 0 ≤ χ i x) (hχ : ∀ i, AEMeasurable (χ i) μ)
    (hF : AEMeasurable (fun x => F x ^ 2) μ) :
    (∀ j, Integrable (fun x => (n01aCoarseLocalizer σ hσ χ j x * F x) ^ 2) μ) ↔
      ∀ i, Integrable (fun x => (χ i x * F x) ^ 2) μ := by
  constructor
  · intro hI i
    refine (hI (σ i)).mono_nonneg
      (n01a_localized_square_aemeasurable μ (hχ i) hF).aestronglyMeasurable
      (Eventually.of_forall fun _ => sq_nonneg _) ?_
    exact Eventually.of_forall fun x =>
      n01a_fine_square_le_coarse_square σ hσ χ hχnonneg i x (F x)
  · intro hI j
    exact n01aCoarseLocalizer_square_integrable μ σ hσ hχ hF hI j

/-- Coarsening compares actual square integrals with the original fine integrals. -/
theorem n01aCoarseLocalizer_integral_bounds (σ : ι → κ)
    (hσ : ∀ j, {i | σ i = j}.Finite) {χ : ι → Ω → ℝ} {F : Ω → ℝ}
    (hχnonneg : ∀ i x, 0 ≤ χ i x) (hχ : ∀ i, AEMeasurable (χ i) μ)
    (hF : AEMeasurable (fun x => F x ^ 2) μ)
    (hI : ∀ i, Integrable (fun x => (χ i x * F x) ^ 2) μ)
    (B : ℕ) (hB : ∀ x, {i | χ i x ≠ 0}.Finite ∧ {i | χ i x ≠ 0}.ncard ≤ B)
    (j : κ) :
    (∑ i ∈ n01aCoarseningFiber σ hσ j, n01aLocalSquare μ χ F i) ≤
      n01aLocalSquare μ (n01aCoarseLocalizer σ hσ χ) F j ∧
    n01aLocalSquare μ (n01aCoarseLocalizer σ hσ χ) F j ≤
      (B : ℝ) * ∑ i ∈ n01aCoarseningFiber σ hσ j, n01aLocalSquare μ χ F i := by
  have hsum := integrable_finsetSum (n01aCoarseningFiber σ hσ j) (fun i _ => hI i)
  have hc := n01aCoarseLocalizer_square_integrable μ σ hσ hχ hF hI j
  constructor
  · have h := integral_mono hsum hc (fun x =>
      n01a_sum_localizer_squares_le (n01aCoarseningFiber σ hσ j)
        (fun i => χ i x) (fun i => hχnonneg i x) (F x))
    simpa only [integral_finsetSum _ (fun i _ => hI i), n01aLocalSquare] using h
  · have h := integral_mono hc (hsum.const_mul (B : ℝ)) (fun x =>
      n01a_square_sum_localizer_le_overlap (n01aCoarseningFiber σ hσ j)
        (fun i => χ i x) B (hB x).1 (hB x).2 (F x))
    simpa only [integral_const_mul, integral_finsetSum _ (fun i _ => hI i),
      n01aLocalSquare] using h

end Measure

end ContinuousFlexibility.Statements
