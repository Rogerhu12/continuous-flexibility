module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05CanonicalSourceCoefficient
public import ContinuousFlexibility.Radial.ProfilePartitionBounds

/-!
# Finite localized source weights on the actual pieces

The source weight is first summed over an arbitrary finite set of reference
localizers. The same constant controls every such finite sum, because the
true nonnegative partition of one has square sum at most one. This permits
deriving the infinite source square sum from integral estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

def n05ReferenceFiniteSourceWeight (D : ReferenceData) (γ M : ℝ)
    (q : Finset ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ q, Real.exp
    (2 * M * radialQ (D.cellIndex j) + 2 * γ * radialS (D.cellIndex j)) *
      D.localizer j r ^ 2

theorem n05ReferenceFiniteSourceWeight_nonneg (D : ReferenceData) (γ M : ℝ)
    (q : Finset ℕ) (r : ℝ) :
    0 ≤ n05ReferenceFiniteSourceWeight D γ M q r :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem n05ReferenceFiniteSourceWeight_continuous {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) (q : Finset ℕ) :
    Continuous (n05ReferenceFiniteSourceWeight D γ M q) := by
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul ((hD.1 j).continuous.pow 2)

theorem n05ReferenceFiniteSourceWeight_singleton (D : ReferenceData) (γ M : ℝ)
    (j : ℕ) (r : ℝ) :
    n05ReferenceFiniteSourceWeight D γ M {j} r =
      Real.exp (2 * M * radialQ (D.cellIndex j) + 2 * γ * radialS (D.cellIndex j)) *
        D.localizer j r ^ 2 := by
  simp only [n05ReferenceFiniteSourceWeight, Finset.sum_singleton]

/-- The constant is independent of the finite localizer family. -/
theorem n05_referenceCanonicalSource_finite_density_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : Finset ℕ) m p, p ∈ referencePhysicalPieceOpen S K m →
      n05ReferenceFiniteSourceWeight D γw M q p.1 *
        (|planeJacobian (K.chart (C.referenceState, 0) m) p| /
          K.height (C.referenceState, 0) m p) ^ 2 *
        n05CanonicalSampleWeight T S K γ t m ^ 2 ≤
          B * |planeJacobian (K.chart (C.referenceState, 0) m) p| := by
  classical
  obtain ⟨B, hB, hb⟩ :=
    n05_referenceCanonicalSource_square_density_bound hD hT h hcoordinates hγw hgap t M
  refine ⟨B, hB, fun q m p hp => ?_⟩
  let J : ℝ := |planeJacobian (K.chart (C.referenceState, 0) m) p|
  let H : ℝ := K.height (C.referenceState, 0) m p
  let w : ℝ := n05CanonicalSampleWeight T S K γ t m
  have hlocal (j : ℕ) :
      (Real.exp (2 * M * radialQ (D.cellIndex j) + 2 * γw * radialS (D.cellIndex j)) *
          D.localizer j p.1 ^ 2) * (J / H) ^ 2 * w ^ 2 ≤
        (B * J) * D.localizer j p.1 ^ 2 := by
    by_cases hj : D.localizer j p.1 = 0
    · simp only [hj, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, le_refl]
    · have hrj : p.1 ∈ D.cells j := hD.choose_spec.2.1.2.2.1 j hj
      have hbound := mul_le_mul_of_nonneg_right (hb m j p hp hrj)
        (sq_nonneg (D.localizer j p.1))
      convert hbound using 1 <;> ring
  calc
    _ = ∑ j ∈ q,
        (Real.exp (2 * M * radialQ (D.cellIndex j) + 2 * γw * radialS (D.cellIndex j)) *
          D.localizer j p.1 ^ 2) * (J / H) ^ 2 * w ^ 2 := by
      rw [n05ReferenceFiniteSourceWeight, Finset.sum_mul, Finset.sum_mul]
    _ ≤ ∑ j ∈ q, (B * J) * D.localizer j p.1 ^ 2 :=
      Finset.sum_le_sum fun j _ => hlocal j
    _ = (B * J) * ∑ j ∈ q, D.localizer j p.1 ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (B * J) * 1 := mul_le_mul_of_nonneg_left
      (Radial.profile_localizer_sq_sum_le_one hD.choose_spec.2.1 q p.1)
      (mul_nonneg hB.le (abs_nonneg _))
    _ = _ := mul_one _

end ContinuousFlexibility.Statements
