import ContinuousFlexibility.Analysis.PositiveReferenceFinitePrescribed

/-!
# Explicit costs of the same prescribed reference interpolation

The finite endpoint data determine one displayed width and hence one
coordinate and height. This lemma packages the reciprocal width,
derivative and reciprocal derivative, and both height values. It does
not replace these functions by an earlier qualitative choice.

The last scalar lemma converts a supplied raw-data envelope into a
material power. It does not assert that the endpoint data or the gap
already have such an envelope for an arbitrary Through03 witness.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem positiveReferenceFiniteRadialJets_prescribed_costs
    (n : ℕ) {l r κ M U : ℝ}
    (hlr : l < r) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hU : 1 ≤ U) (hMU : M ≤ U) (hκU : κ⁻¹ ≤ U)
    (hgapU : (r - l)⁻¹ ≤ U) (hspanU : r - l ≤ U)
    {a b : Bool → ℝ} {y h : Bool → PolarPoint → ℝ}
    (hab : ∀ side, a side < b side)
    (hc : ∀ side : Bool, (if side then r else l) ∈ Icc (a side) (b side))
    (hy : ∀ side, ContDiffOn ℝ ∞ (y side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hh : ∀ side, ContDiffOn ℝ ∞ (h side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hyc : ∀ (side : Bool) θ, ContDiffAt ℝ ∞ (y side) (if side then r else l, θ))
    (hhc : ∀ (side : Bool) θ, ContDiffAt ℝ ∞ (h side) (if side then r else l, θ))
    (hyr : ∀ side x, x ∈ Ioo (a side) (b side) → ∀ θ,
      y side (x, θ) = y side (x, 0))
    (hhr : ∀ side x, x ∈ Ioo (a side) (b side) → ∀ θ,
      h side (x, θ) = h side (x, 0))
    (hyvalue : ∀ side : Bool, y side (if side then r else l, 0) =
      (if side then (1 : ℝ) else 0))
    (hyslope : ∀ side : Bool, κ ≤ radialBoundaryJet (y side) (if side then r else l) 1 0)
    (hhpositive : ∀ side : Bool, κ ≤ radialBoundaryJet (h side) (if side then r else l) 0 0)
    (hybound : ∀ (side : Bool) j, 1 ≤ j → j ≤ n + 1 →
      |radialBoundaryJet (y side) (if side then r else l) j 0| ≤ M)
    (hhbound : ∀ (side : Bool) j, j ≤ n + 1 →
      |radialBoundaryJet (h side) (if side then r else l) j 0| ≤ M) :
    let δ := positiveReferenceTaylorWidth n l r κ M
    let ys := fun side : Bool => radialEndpointTaylorSlice (n + 1)
      (if side then r else l) (y side)
    let hs := fun side : Bool => radialEndpointTaylorSlice (n + 1)
      (if side then r else l) (h side)
    let Y := positiveReferenceCoordinate l r δ (deriv (ys false)) (deriv (ys true))
    let H := positiveReferenceHeight l r δ (hs false) (hs true)
    0 < δ ∧ δ ≤ 1 ∧
      δ⁻¹ ≤ (24 + 16 * ((n + 2 : ℕ) : ℝ)) * U ^ 2 ∧
      ∀ x, 0 < deriv Y x ∧ deriv Y x ≤ ((n + 2 : ℕ) : ℝ) * U ∧
        (deriv Y x)⁻¹ ≤ 2 * U ∧ 0 < H x ∧
          H x ≤ 4 * U ^ 2 ∧ (H x)⁻¹ ≤ 4 * U ^ 2 := by
  let δ := positiveReferenceTaylorWidth n l r κ M
  let ys : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (if side then r else l) (y side)
  let hs : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (if side then r else l) (h side)
  let Y := positiveReferenceCoordinate l r δ (deriv (ys false)) (deriv (ys true))
  let H := positiveReferenceHeight l r δ (hs false) (hs true)
  let A : ℝ := ((n + 2 : ℕ) : ℝ)
  have hA : 2 ≤ A := by
    change (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ)
    exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hspan : 0 < r - l := sub_pos.mpr hlr
  have hfactory := positiveReferenceFiniteRadialJets_prescribed n hlr hκ hM
    hab hc hy hh hyc hhc hyr hhr hyvalue hyslope hhpositive hybound hhbound
  dsimp only at hfactory
  have hκmul : (1 : ℝ) ≤ κ * U := by
    simpa only [mul_inv_cancel₀ hκ.ne'] using
      mul_le_mul_of_nonneg_left hκU hκ.le
  have hκlower : 1 / (2 * U) ≤ κ / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * U)).2
    nlinarith only [hκmul]
  have hgaplower : 1 / (2 * U) ≤ 1 / (2 * (r - l)) :=
    one_div_le_one_div_of_le (by positivity : 0 < 2 * (r - l))
      (mul_le_mul_of_nonneg_left hspanU (by norm_num))
  have hMupper : M + ((n + 1 : ℕ) : ℝ) * M ≤ A * U := by
    have he : M + ((n + 1 : ℕ) : ℝ) * M = A * M := by
      dsimp only [A]
      push_cast
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hMU hA0
  have hgapupper : 2 / (r - l) ≤ A * U := by
    calc
      _ = 2 * (r - l)⁻¹ := div_eq_mul_inv _ _
      _ ≤ 2 * U := mul_le_mul_of_nonneg_left hgapU (by norm_num)
      _ ≤ A * U := mul_le_mul_of_nonneg_right hA hUpos.le
  let V : ℝ := max 1 (max (2 * M) (2 / κ))
  have hV : V ≤ 2 * U := by
    apply max_le
    · linarith only [hU]
    · apply max_le
      · exact mul_le_mul_of_nonneg_left hMU (by norm_num)
      · simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hκU (show (0 : ℝ) ≤ 2 by norm_num)
  have hV0 : 0 ≤ V := zero_le_one.trans (le_max_left _ _)
  have hV2 : V ^ 2 ≤ 4 * U ^ 2 := by
    calc
      _ ≤ (2 * U) ^ 2 := pow_le_pow_left₀ hV0 hV 2
      _ = _ := by ring
  have hδdata := positiveReferenceTaylorWidth_margins n hlr hκ hM
  refine ⟨hδdata.1, hδdata.2.1,
    positiveReferenceTaylorWidth_polynomial_inv_le n hlr hκ hM hU hMU hκU hgapU, ?_⟩
  intro x
  have hd : min (κ / 2) (1 / (2 * (r - l))) ≤ deriv Y x ∧
      deriv Y x ≤ max (M + ((n + 1 : ℕ) : ℝ) * M) (2 / (r - l)) :=
    hfactory.2.2.2.1 x
  have hdlower : 1 / (2 * U) ≤ deriv Y x :=
    (le_min hκlower hgaplower).trans hd.1
  have hdpos : 0 < deriv Y x :=
    (by positivity : 0 < 1 / (2 * U)).trans_le hdlower
  have hdinv : (deriv Y x)⁻¹ ≤ 2 * U := by
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le (by positivity : 0 < 1 / (2 * U)) hdlower
  have hheight : H x ≤ V ^ 2 ∧ (H x)⁻¹ ≤ V ^ 2 := hfactory.2.2.2.2 x
  exact ⟨hdpos, hd.2.trans (max_le hMupper hgapupper), hdinv,
    hfactory.1.height_positive (x, 0),
    hheight.1.trans hV2, hheight.2.trans hV2⟩

/-- A polynomial cost for the displayed width converts to a fixed power
of the very same material base. Establishing the input envelope from
actual root data is a separate theorem. -/
theorem positiveReferencePrescribedCost_material_bound (n : ℕ)
    {U K W : ℝ} (hU : 0 ≤ U) (hUW : U ≤ K * W ^ K) (hW : 1 ≤ W) :
    (24 + 16 * ((n + 2 : ℕ) : ℝ)) * U ^ 2 ≤
      ((24 + 16 * ((n + 2 : ℕ) : ℝ)) * K ^ 2) * W ^ (2 * K) := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  calc
    _ ≤ (24 + 16 * ((n + 2 : ℕ) : ℝ)) * (K * W ^ K) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU hUW 2) (by positivity)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hW0 K 2]
      rw [show K * (2 : ℝ) = 2 * K by ring]
      ring

end ContinuousFlexibility.Analysis
