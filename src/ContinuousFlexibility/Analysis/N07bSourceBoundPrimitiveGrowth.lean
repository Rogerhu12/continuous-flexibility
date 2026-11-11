import ContinuousFlexibility.Analysis.N07bSourceBoundPrimitiveJets
import ContinuousFlexibility.Analysis.N07bSourceBoundNeighborhood
import ContinuousFlexibility.Scalar.WeightedCoefficientAlgebra

/-!
# Uniform source coefficient bounds from primitive geometric growth

A fixed finite jet estimate on the four primitive fields is enough. The
positive exponent `1/(b+1)` allocates one material-envelope power to a
whole path. Squaring gives the `M²` comparison required by source energy.
A fixed state polynomial is absorbed by increasing the common low order
and shrinking its radius, before the state or source is chosen.

The geometric growth predicates below are explicit hypotheses, not fields
silently extracted from frozen `N04PartA`. They contain no source function,
Banach inverse, or estimate on any recursively generated coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A genuine primitive-field estimate with a fixed state polynomial and
one common material power. All witnesses precede the state and piece. -/
def N07bSourcePrimitiveGrowth (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (b : ℕ) : Prop :=
  ∃ r d : ℕ, ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m y, y ∈ n07bSourceMaterialPiece T K z m →
        N07bSourcePrimitiveJetBound T K z m b
          (C₀ * T.M (T.radius y.1) ^ (1 / ((b + 1 : ℕ) : ℝ)) *
            (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d) y

/-- A common `E0` exponent is an alternative primitive geometry input.
There is no assumption that `E0` is at least one. -/
def N07bSourcePrimitiveE0Growth (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (b : ℕ) : Prop :=
  ∃ r d : ℕ, ∃ C₀ A : ℝ, 0 ≤ C₀ ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m y, y ∈ n07bSourceMaterialPiece T K z m →
        N07bSourcePrimitiveJetBound T K z m b
          (C₀ * T.E0 (T.radius y.1) ^ A *
            (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d) y

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base b : ℕ} {ε : ℝ}

/-- The existing material subpower theorem supplies precisely the power
needed for the finite coefficient recursion. -/
theorem n07b_sourcePrimitiveGrowth_of_E0 (hT : IsMaterialData D T)
    (h : N07bSourcePrimitiveE0Growth T S C K base ε b) :
    N07bSourcePrimitiveGrowth T S C K base ε b := by
  obtain ⟨r, d, C₀, A, hC₀, hbound⟩ := h
  have hδ : 0 < 1 / ((b + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨CA, hCA, hEA⟩ := materialE0_rpow_le_subpowerM hT A hδ
  refine ⟨r, d, max 1 (C₀ * CA), le_max_left _ _, ?_⟩
  intro z hz hs m y hy
  have hycore := (hT.2.2.2.2.2.2.2.1 y.1).1
  have hM : 0 ≤ T.M (T.radius y.1) := zero_le_one.trans (hT.2.1 _ hycore).2.2.2
  have hQ : 0 ≤ 1 + stateGrading S r (z.1 - C.referenceState) + |z.2| :=
    add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _)
  apply (hbound z hz hs m y hy).mono
  calc
    _ ≤ C₀ * (CA * T.M (T.radius y.1) ^ (1 / ((b + 1 : ℕ) : ℝ))) *
        (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hEA _ hycore) hC₀) (pow_nonneg hQ _)
    _ = (C₀ * CA) * T.M (T.radius y.1) ^ (1 / ((b + 1 : ℕ) : ℝ)) *
        (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 (C₀ * CA)) (Real.rpow_nonneg hM _))
      (pow_nonneg hQ _)

private theorem primitiveRadius_one_le (b d : ℕ) {C₀ M Q : ℝ}
    (hC : 1 ≤ C₀) (hM : 1 ≤ M) (hQ : 1 ≤ Q) :
    1 ≤ C₀ * M ^ (1 / ((b + 1 : ℕ) : ℝ)) * Q ^ d := by
  have hMp : 1 ≤ M ^ (1 / ((b + 1 : ℕ) : ℝ)) :=
    Real.one_le_rpow hM (by positivity)
  have hQp : 1 ≤ Q ^ d := one_le_pow₀ hQ
  have hCM : 1 ≤ C₀ * M ^ (1 / ((b + 1 : ℕ) : ℝ)) := by
    simpa only [one_mul] using mul_le_mul hC hMp zero_le_one (zero_le_one.trans hC)
  simpa only [one_mul] using mul_le_mul hCM hQp zero_le_one (zero_le_one.trans hCM)

private theorem primitiveRadius_power (b d : ℕ) (C₀ M Q : ℝ) (hM : 0 ≤ M) :
    (n07bSourceChainJetConstant b ^ b *
      (C₀ * M ^ (1 / ((b + 1 : ℕ) : ℝ)) * Q ^ d) ^ (b + 1)) ^ 2 =
      (n07bSourceChainJetConstant b ^ b * C₀ ^ (b + 1)) ^ 2 * M ^ 2 *
        Q ^ (d * (b + 1) * 2) := by
  have hden : ((b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hroot : (M ^ (1 / ((b + 1 : ℕ) : ℝ))) ^ (b + 1) = M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM,
      div_mul_cancel₀ (1 : ℝ) hden, Real.rpow_one]
  simp only [mul_pow, hroot, ← pow_mul]
  ring

/-- Only primitive jet bounds are assumed. The actual recursion supplies
the weighted estimate for every retained source coefficient. -/
theorem n07b_sourceCoefficient_M_polynomial_of_primitive_growth
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε)
    (h : N07bSourcePrimitiveGrowth T S C K base ε b) :
    ∃ r d : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ m x, x ∈ physicalPieceOpen S K z m →
          ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
            n07bSourceGeometricWeight T K z m x *
                n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
              A * T.M x.1 ^ 2 *
                (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d := by
  obtain ⟨r, d, C₀, hC₀, hbound⟩ := h
  refine ⟨r, d * (b + 1) * 2,
    (n07bSourceChainJetConstant b ^ b * C₀ ^ (b + 1)) ^ 2, sq_nonneg _, ?_⟩
  intro z hz hs m x hx j i
  have hxcore : x.1 ∈ Ioo D.a D.b := ((hK.domains z hz hs m).2.2.1 hx).1
  have hy : n07bMaterialChart T x ∈ n07bSourceMaterialPiece T K z m := by
    change n07bMaterialRadiusChart T (n07bMaterialChart T x) ∈ physicalPieceOpen S K z m
    rw [n07bMaterialRadiusChart_materialChart hT hxcore]
    exact hx
  have hradius : T.radius (n07bMaterialChart T x).1 = x.1 := by
    change T.radius (T.rho x.1) = x.1
    exact hT.2.2.2.2.2.2.2.2.1 x.1 hxcore
  have hjets := hbound z hz hs m (n07bMaterialChart T x) hy
  rw [hradius] at hjets
  have hM : 1 ≤ T.M x.1 := (hT.2.1 x.1 hxcore).2.2.2
  have hQ : 1 ≤ 1 + stateGrading S r (z.1 - C.referenceState) + |z.2| := by
    linarith [apply_nonneg (stateGrading S r) (z.1 - C.referenceState), abs_nonneg z.2]
  have hsquare := n07b_sourcePrimitive_weighted_square_le hD hT hK hz hs m b hx
    (primitiveRadius_one_le b d hC₀ hM hQ) hjets (Nat.le_of_lt_succ j.isLt) i
  exact hsquare.trans_eq (primitiveRadius_power b d C₀ (T.M x.1)
    (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) (zero_le_one.trans hM))

/-- All state growth in a fixed primitive jet bound is absorbed on one
common smaller neighborhood. The charts themselves are unchanged. -/
theorem n07b_exists_uniform_sourceCoefficient_M_bound_of_primitive
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hε : 0 < ε)
    (h : N07bSourcePrimitiveGrowth T S C K base ε b) :
    ∃ base' : ℕ, ∃ ε' A : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ (1 / 2 : ℝ) ∧ 0 ≤ A ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
        ∀ m x, x ∈ physicalPieceOpen S K z m →
          ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
            n07bSourceGeometricWeight T K z m x *
                n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
              A * T.M x.1 ^ 2 := by
  obtain ⟨r, d, A, hA, hcoeff⟩ :=
    n07b_sourceCoefficient_M_polynomial_of_primitive_growth hD hT hK h
  refine ⟨max base r, min ε (1 / 2), A * (2 : ℝ) ^ d,
    le_max_left _ _, lt_min hε (by norm_num), min_le_left _ _, min_le_right _ _,
    mul_nonneg hA (pow_nonneg (by norm_num) _), ?_⟩
  intro z hz hs m x hx j i
  have hzold := n06_stateNeighborhood_mono (C := C)
    (le_max_left base r) (min_le_left ε (1 / 2)) hz
  have hQ := n07b_stateWeight_pow_le_two_pow (d := d)
    (le_max_right base r) (min_le_right ε (1 / 2)) hz
  calc
    _ ≤ A * T.M x.1 ^ 2 *
        (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d :=
      hcoeff z hzold hs m x hx j i
    _ ≤ A * T.M x.1 ^ 2 * (2 : ℝ) ^ d :=
      mul_le_mul_of_nonneg_left hQ (mul_nonneg hA (sq_nonneg _))
    _ = _ := by ring

end ContinuousFlexibility.Analysis
