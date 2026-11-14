module

public import ContinuousFlexibility.Analysis.StateNeighborhood
public import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Uniform absorption of geometric coefficient powers

The material envelope dominates every power of `E0`, while every positive
power of `H` absorbs the envelope. Together these existing material
properties give a uniform coefficient bound, including all sampled cells.
Consequently a fixed low-order state displacement can be made uniformly
small on one smaller state neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- A genuine first-variation bound becomes uniformly small after a single
base-order increase and radius decrease. The order `high` is fixed before
this choice, and all cells and spatial points use the same new radius. -/
theorem exists_stateNeighborhood_uniform_smallness
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base high : ℕ} {ε : ℝ} {ι : Type*}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (Q : AnnularState S × ℝ → Prop)
    (κ : ℕ → ℕ) (V : ℕ → Set ι)
    (F : AnnularState S × ℝ → ℕ → ι → ℝ)
    {B β K : ℝ} (hB : 0 < B) (hβ : 0 < β) (hK : 0 < K)
    (hbound : ∀ z ∈ stateNeighborhood S C base ε, Q z →
      ∀ m p, p ∈ V m → |F z m p| ≤
        B * T.H (T.sample (κ m)) ^ β * T.E0 (T.sample (κ m)) ^ B * K *
          (stateGrading S high (z.1 - C.referenceState) + |z.2|))
    {η : ℝ} (hη : 0 < η) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ high ≤ base' ∧
      0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C base' ε', Q z →
        ∀ m p, p ∈ V m → |F z m p| < η := by
  obtain ⟨M, hM, hMb⟩ :=
    material_sample_height_coefficient_power_bounded hD hT κ B hβ
  let ε' : ℝ := min ε (η / (4 * (B * M * K)))
  have hBM : 0 < B * M * K := mul_pos (mul_pos hB hM) hK
  have hε' : 0 < ε' := lt_min hε (div_pos hη (mul_pos (by norm_num) hBM))
  refine ⟨max base high, ε', le_max_left _ _, le_max_right _ _, hε',
    min_le_left _ _, ?_⟩
  intro z hz hs m p hp
  have hzold := stateNeighborhood_mono S C (le_max_left base high) (min_le_left _ _) hz
  have hhigh : stateGrading S high (z.1 - C.referenceState) < ε' :=
    (stateGrading_monotone S (le_max_right base high) _).trans_lt hz.1
  have hdispl : stateGrading S high (z.1 - C.referenceState) + |z.2| < 2 * ε' := by
    linarith [hz.2]
  have hnonneg : 0 ≤ stateGrading S high (z.1 - C.referenceState) + |z.2| :=
    add_nonneg (apply_nonneg _ _) (abs_nonneg _)
  have hcoef : B * T.H (T.sample (κ m)) ^ β * T.E0 (T.sample (κ m)) ^ B * K ≤
      B * M * K := by
    apply mul_le_mul_of_nonneg_right _ hK.le
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hMb m) hB.le
  calc
    |F z m p| ≤
        B * T.H (T.sample (κ m)) ^ β * T.E0 (T.sample (κ m)) ^ B * K *
          (stateGrading S high (z.1 - C.referenceState) + |z.2|) :=
      hbound z hzold hs m p hp
    _ ≤ B * M * K * (stateGrading S high (z.1 - C.referenceState) + |z.2|) :=
      mul_le_mul_of_nonneg_right hcoef hnonneg
    _ < B * M * K * (2 * ε') := mul_lt_mul_of_pos_left hdispl hBM
    _ ≤ B * M * K * (2 * (η / (4 * (B * M * K)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (min_le_right ε _) (by norm_num)) hBM.le
    _ = η / 2 := by field_simp [hBM.ne']; ring
    _ < η := by linarith

end ContinuousFlexibility.Analysis
