module

public import ContinuousFlexibility.Analysis.N08NormalizedCellProfile
public import ContinuousFlexibility.Analysis.N08RadialPositiveWeightBounds
public import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Uniformly bounded actual height directions with positive cell slope

The same realized height family works at every grading. Its decoded radial
function and its genuine derivative are fixed before choosing a negative
component or a requested norm order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n08NormalizedCellHeight (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {A : ℝ} (hA : 0 < A) (m : ℕ) : (S.height (3 / 4 : ℝ)).Space :=
  Classical.choose ((hS.1 (3 / 4 : ℝ)).2.2.2.2.1 _
    (n08NormalizedCellProfile_heightMember hT hA m (3 / 4 : ℝ)))

theorem n08NormalizedCellHeight_decode (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {A : ℝ} (hA : 0 < A) (m : ℕ) :
    (S.height (3 / 4 : ℝ)).decode (n08NormalizedCellHeight hT hS hA m) =
      fun p : PolarPoint => n08NormalizedCellProfile D T A m p.1 :=
  Classical.choose_spec ((hS.1 (3 / 4 : ℝ)).2.2.2.2.1 _
    (n08NormalizedCellProfile_heightMember hT hA m (3 / 4 : ℝ)))

def n08NormalizedCellDirection (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {A : ℝ} (hA : 0 < A) (m : ℕ) : HeightPair S :=
  (n08NormalizedCellHeight hT hS hA m, 0)

theorem n08NormalizedCellDirection_field (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {A : ℝ} (hA : 0 < A) (m : ℕ) (p : PolarPoint) :
    heightPairField S (n08NormalizedCellDirection hT hS hA m) p =
      n08NormalizedCellProfile D T A m p.1 := by
  change (S.height (3 / 4 : ℝ)).decode (n08NormalizedCellHeight hT hS hA m) p +
    (0 : ℝ) * S.chiLeft p.1 = _
  rw [n08NormalizedCellHeight_decode, zero_mul, add_zero]

theorem n08NormalizedCellDirection_grading_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {A : ℝ} (hA : 1 ≤ A) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m,
      heightPairGrading S s
        (n08NormalizedCellDirection hT hS (zero_lt_one.trans_le hA) m) ≤ K := by
  have hF (m : ℕ) : ContDiffOn ℝ ∞ (n08NormalizedCellProfile D T A m) (Ioo D.a D.b) :=
    (n08NormalizedCellProfile_contDiff D T A m).contDiffOn
  have hb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m r, r ∈ Ioo D.a D.b →
      |iteratedDeriv n (n08NormalizedCellProfile D T A m) r| ≤
        K * T.H r ^ (2 * (3 / 4 : ℝ)) := by
    intro n
    simpa only [show 2 * (3 / 4 : ℝ) = 3 / 2 by norm_num] using
      n08NormalizedCellProfile_jet_bound hD hT hA n
  obtain ⟨K, hK, hKb⟩ := n08_radialPositive_physicalNorm_bound hT
    (by norm_num : (0 : ℝ) < 3 / 4) hF hb s
  refine ⟨K, hK, fun m => ?_⟩
  change (S.height (3 / 4 : ℝ)).grading s
    (n08NormalizedCellHeight hT hS (zero_lt_one.trans_le hA) m) + |(0 : ℝ)| ≤ K
  rw [abs_zero, add_zero, sobolevGrading_eq_physicalNorm (hS.1 (3 / 4 : ℝ)),
    n08NormalizedCellHeight_decode]
  exact hKb m

/-- The fixed family has the required positive slope on every reference
cell, and one bound for all members at each requested norm order. -/
theorem n08_exists_normalized_cell_tests
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) :
    ∃ η : ℕ → HeightPair S, ∃ h g : ℕ → ℝ → ℝ,
      (∀ m r, HasDerivAt (h m) (g m r) r) ∧
      (∀ m p, heightPairField S (η m) p = h m p.1) ∧
      (∀ m r, r ∈ D.cells m → g m r = T.H (T.sample m) ^ (32 : ℝ)) ∧
      (∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m, heightPairGrading S s (η m) ≤ K) := by
  obtain ⟨A, hA, hplateau⟩ := n08_referenceCell_layer_parameters hD
  let h : ℕ → ℝ → ℝ := n08NormalizedCellProfile D T A
  refine ⟨n08NormalizedCellDirection hT hS (zero_lt_one.trans_le hA), h,
    fun m => deriv (h m), ?_, ?_, ?_, ?_⟩
  · intro m r
    exact ((n08NormalizedCellProfile_contDiff D T A m).differentiable (by simp) r).hasDerivAt
  · intro m p
    exact n08NormalizedCellDirection_field hT hS (zero_lt_one.trans_le hA) m p
  · intro m r hr
    exact (n08NormalizedCellProfile_hasDerivAt (zero_lt_one.trans_le hA) m (hplateau m r hr)).deriv
  · exact n08NormalizedCellDirection_grading_bound hD hT hS hA

end ContinuousFlexibility.Statements
