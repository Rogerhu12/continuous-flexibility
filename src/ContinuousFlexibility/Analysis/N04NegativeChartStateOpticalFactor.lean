module

public import ContinuousFlexibility.Analysis.N04NegativeChartOpticalFactorBounds
public import ContinuousFlexibility.Analysis.N04NegativeChartControlDivision
public import ContinuousFlexibility.Analysis.N01NegativeOpticalLower

/-!
# The actual affine optical factor on each complete negative half

The reference optical division and the control division are chosen
before all states and jet orders. Their affine combination factors the
actual state optical square. On one common state neighborhood it stays
above half the reference factor, including the root, so its reciprocal
has the same sampled polynomial cost. No profile-identity collar enters.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

variable (W : N04RealizationStart)

theorem negativeOpticalWidth_lt_component (m : ℕ) (side : Bool) :
    W.negativeOpticalWidth m side < W.C.right m - W.C.left m := by
  have hc := n04bActualReferenceCut_mem W.through03 m
  cases side <;> simp only [negativeOpticalWidth, n04bNegativeRight,
    n04bNegativeLeft, Bool.false_eq_true, ↓reduceIte] <;> linarith only [hc.1, hc.2]

/-- The two actual smooth divisions, with their already proved material
bounds, retained as the same pair for every subsequent operation. -/
structure NegativeOpticalFactors (e : ℕ ≃ N04PieceIndex W.D) where
  reference : ℕ → Bool → ℝ → ℝ
  control : ℕ → Bool → ℝ → ℝ
  reference_smooth : ∀ m side, ContDiff ℝ ∞ (reference m side)
  control_smooth : ∀ m side, ContDiff ℝ ∞ (control m side)
  control_zero : ∀ m side, control m side 0 = 0
  reference_divides : ∀ m side t, t ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) →
    n01aOpticalRadicand W.D.w
      (inwardComponentPoint (W.C.left m) (W.C.right m) side t) = t * reference m side t
  control_divides : ∀ m side t, controlOpticalFactor W.C m
    (inwardComponentPoint (W.C.left m) (W.C.right m) side t) = t * control m side t
  reference_pos : ∀ m side t, t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
    0 < reference m side t
  reference_powers : ∀ a : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
    ∀ m side t, t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) → ∀ n,
      |iteratedDeriv n (fun x => reference m side x ^ a) t| ≤
        B n * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (B n)
  control_jets : ∀ n : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m side t,
    t ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) →
      |iteratedDeriv n (control m side) t| ≤ B * W.T.E0 (W.T.sample (W.C.cell m)) ^ A

theorem negativeOpticalFactors_nonempty (e : ℕ ≃ N04PieceIndex W.D) :
    Nonempty (NegativeOpticalFactors W e) := by
  obtain ⟨r, hrs, hrd, hrp, hrb⟩ := W.negativeOpticalFactor_power_material_jets e
  obtain ⟨c, hcs, hcz, hcd, hcb⟩ := W.negativeControlDivision_material_jets
  exact ⟨⟨r, c, hrs, hcs, hcz, hrd, hcd, hrp, hrb, hcb⟩⟩

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

/-- This is the exact quotient of the actual optical square by the
inward physical root variable. Its state dependence is affine. -/
def stateSquare (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) (t : ℝ) : ℝ :=
  F.reference m side t - stateKappa W.S z.1 m * F.control m side t

theorem stateSquare_contDiff (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) :
    ContDiff ℝ ∞ (F.stateSquare z m side) :=
  (F.reference_smooth m side).sub (contDiff_const.mul (F.control_smooth m side))

theorem stateSquare_reference (m : ℕ) (side : Bool) :
    F.stateSquare (W.C.referenceState, 0) m side = F.reference m side := by
  have hk : stateKappa W.S W.C.referenceState m = 0 := by
    simpa only [zero_smul, add_zero, zero_mul] using
      n04b_stateKappa_reference_line W.through03.1.1.2.2.1
        (0 : AnnularState W.S) 0 m
  funext t
  simp only [stateSquare, hk, zero_mul, sub_zero]

theorem stateSquare_actual (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (W.C.right m - W.C.left m)) :
    n01aOpticalRadicand (stateProfile W.D W.S W.C z.1)
      (inwardComponentPoint (W.C.left m) (W.C.right m) side t) =
        t * F.stateSquare z m side t := by
  have h01 := W.through03.1.1
  have hA : N01PartA W.D W.T W.S W.C :=
    ⟨h01.1, h01.2.2.1, h01.2.2.2.1, h01.2.2.2.2.1, h01.2.2.2.2.2.1⟩
  have hr : inwardComponentPoint (W.C.left m) (W.C.right m) side t ∈
      Ioo (W.C.left m) (W.C.right m) := by
    cases side <;> simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
      <;> constructor <;> linarith only [ht.1, ht.2]
  calc
    _ = n01aOpticalRadicand W.D.w
        (inwardComponentPoint (W.C.left m) (W.C.right m) side t) -
        stateKappa W.S z.1 m * controlOpticalFactor W.C m
          (inwardComponentPoint (W.C.left m) (W.C.right m) side t) := by
      simpa only [n01aOpticalRadicand, controlOpticalFactor, mul_div_assoc] using
        n01_stateProfile_opticalSquare_eq hA z.1 m hr
    _ = t * F.stateSquare z m side t := by
      rw [F.reference_divides m side t ⟨ht.1.le, ht.2.le⟩, F.control_divides]
      dsimp only [stateSquare]
      ring

/-- The radius is fixed before the component. The endpoint follows
from the true zero of the control division, without a limiting radius. -/
theorem stateSquare_reference_half_lower
    {z : AnnularState W.S × ℝ}
    (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (m : ℕ) (side : Bool) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) :
    F.reference m side t / 2 ≤ F.stateSquare z m side t := by
  by_cases ht0 : t = 0
  · subst t
    have hp := F.reference_pos m side 0 ht
    simp only [stateSquare, F.control_zero, mul_zero, sub_zero]
    linarith only [hp]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htfull : t < W.C.right m - W.C.left m :=
    ht.2.trans_lt (W.negativeOpticalWidth_lt_component m side)
  have hr : inwardComponentPoint (W.C.left m) (W.C.right m) side t ∈
      Ioo (W.C.left m) (W.C.right m) := by
    cases side <;> simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
      <;> constructor <;> linarith only [htpos, htfull]
  have h := W.through03.1.1.n04Coordinates_stateProfile_opticalRadicand_half
    W.hS W.hT hz.1 m hr
  change n01aOpticalRadicand W.D.w
      (inwardComponentPoint (W.C.left m) (W.C.right m) side t) / 2 <
    n01aOpticalRadicand (stateProfile W.D W.S W.C z.1)
      (inwardComponentPoint (W.C.left m) (W.C.right m) side t) at h
  rw [F.reference_divides m side t ⟨ht.1, htfull.le⟩,
    F.stateSquare_actual z m side ⟨htpos, htfull⟩] at h
  have hmul : t * (F.reference m side t / 2) ≤ t * F.stateSquare z m side t := by
    nlinarith only [h]
  exact le_of_mul_le_mul_left hmul htpos

theorem stateSquare_pos
    {z : AnnularState W.S × ℝ}
    (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (m : ℕ) (side : Bool) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) :
    0 < F.stateSquare z m side t :=
  (half_pos (F.reference_pos m side t ht)).trans_le
    (F.stateSquare_reference_half_lower hz m side ht)

/-- The reciprocal is bounded at the sample of the actual selected
half, uniformly in every state in the same neighborhood. -/
theorem stateSquare_inverse_material :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2), ∀ m side t,
        t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
          (F.stateSquare z m side t)⁻¹ ≤
            B * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ A := by
  obtain ⟨C, hC, hb⟩ := F.reference_powers (-1)
  refine ⟨2 * C 0, C 0, mul_pos (by norm_num) (hC 0), hC 0, ?_⟩
  intro z hz m side t ht
  have hp := F.reference_pos m side t ht
  have hbound : (F.reference m side t)⁻¹ ≤ C 0 *
      W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (C 0) := by
    simpa only [iteratedDeriv_zero, Real.rpow_neg_one, abs_of_pos (inv_pos.mpr hp)] using
      hb m side t ht 0
  calc
    _ ≤ (F.reference m side t / 2)⁻¹ :=
      inv_anti₀ (half_pos hp) (F.stateSquare_reference_half_lower hz m side ht)
    _ = 2 * (F.reference m side t)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ 2 * (C 0 * W.T.E0
        (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (C 0)) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

end NegativeOpticalFactors

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.stateSquare_inverse_material' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.stateSquare_inverse_material
