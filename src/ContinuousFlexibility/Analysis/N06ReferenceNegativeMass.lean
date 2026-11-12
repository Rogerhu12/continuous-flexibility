import ContinuousFlexibility.Analysis.N06ReferenceNegativeInverse
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Actual reciprocal mass and endpoint bounds for the negative reference height

The true scalar inverse has absolute Jacobian `w / W^2`.  The one-dimensional
change-of-variables theorem therefore identifies the reciprocal mass with
the physical integral of `1 / w` over its actual image, for either orientation.
The genuine determinant formula and global physical profile bounds also
give a polynomial upper bound for `W(y)` when `y > 0`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

private theorem n06_negative_closed_core
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) :
    Icc (K.physicalLeft i) (K.physicalRight i) ⊆ radialCore D := by
  obtain ⟨m, hm⟩ := n06_negativePiece_is_cutHalf h.2.2.2.2 h.1.1.1.2.2.2.1 hi
  exact n06_cutPiece_closed_subset h m hm

/-- The actual Liouville normalization gives the exact absolute Jacobian
needed for the reciprocal-mass change of variables. -/
theorem N06ReferenceNegativeInverseData.reciprocalHeight_jacobian
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {y : ℝ} (hy : y ∈ Icc (K.left i) (K.right i)) :
    |deriv P.inverse y| * (D.w (P.inverse y))⁻¹ = (P.reciprocalHeight y)⁻¹ ^ 2 := by
  have hd := n06_reference_negative_height_normalization hT hS h hi (P.mapsTo hy)
  have hnorm := hd.2.2.2.2.1
  have hcore := n06_negative_closed_core h hi (P.mapsTo hy)
  have hw : D.w (P.inverse y) ≠ 0 :=
    (h.1.1.1.1.1.choose_spec.1.2.2.2.2.1 _ hcore).ne'
  rw [(P.hasDerivAt y hy).deriv, abs_inv]
  change |deriv (n06ReferenceNegativeY C K i) (P.inverse y)|⁻¹ *
    (D.w (P.inverse y))⁻¹ =
      ((n06ReferenceNegativeH C K i (P.inverse y))⁻¹)⁻¹ ^ 2
  rw [inv_inv]
  field_simp [abs_ne_zero.mpr hd.2.2.2.1, hw]
  nlinarith only [hnorm]

/-- This is a change of variables for the actual inverse, not a formal
identity involving values assigned to the original inverse at endpoints. -/
theorem N06ReferenceNegativeInverseData.reciprocal_mass_change
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc (K.left i) (K.right i)) :
    (∫ y in a..b, (P.reciprocalHeight y)⁻¹ ^ 2) =
      ∫ r in P.inverse '' Icc a b, (D.w r)⁻¹ := by
  have hderiv (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivWithinAt P.inverse (deriv P.inverse y) (Icc a b) y :=
    ((P.smooth y (hsub hy)).differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
  have hinj : InjOn P.inverse (Icc a b) := by
    intro x hx y hy he
    calc
      x = n06ReferenceNegativeY C K i (P.inverse x) := (P.right_inverse x (hsub hx)).symm
      _ = n06ReferenceNegativeY C K i (P.inverse y) := congrArg _ he
      _ = y := P.right_inverse y (hsub hy)
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj
    (fun r => (D.w r)⁻¹)
  calc
    (∫ y in a..b, (P.reciprocalHeight y)⁻¹ ^ 2) =
        ∫ y in Icc a b, (P.reciprocalHeight y)⁻¹ ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
    _ = ∫ y in Icc a b, |deriv P.inverse y| • (D.w (P.inverse y))⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      simpa only [smul_eq_mul] using (P.reciprocalHeight_jacobian hT hS h hi (hsub hy)).symm
    _ = ∫ r in P.inverse '' Icc a b, (D.w r)⁻¹ := hchange.symm

/-- Reciprocal mass over any canonical subinterval is bounded by the
physical reciprocal-profile mass of the same selected negative piece. -/
theorem N06ReferenceNegativeInverseData.reciprocal_mass_le_physical
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc (K.left i) (K.right i)) :
    (∫ y in a..b, (P.reciprocalHeight y)⁻¹ ^ 2) ≤
      ∫ r in (K.physicalLeft i)..(K.physicalRight i), (D.w r)⁻¹ := by
  have hgeom : RadialProfileGeometry D := h.1.1.1.1.1.choose_spec.1
  have hwpos (r : ℝ) (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
      0 < D.w r := hgeom.2.2.2.2.1 r (n06_negative_closed_core h hi hr)
  have hcont : ContinuousOn (fun r => (D.w r)⁻¹)
      (Icc (K.physicalLeft i) (K.physicalRight i)) :=
    hgeom.2.2.1.1.continuous.continuousOn.inv₀ (fun r hr => (hwpos r hr).ne')
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (K.physicalLeft i) (K.physicalRight i))]
      (fun r => (D.w r)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (inv_pos.mpr (hwpos r hr)).le
  have himage : P.inverse '' Icc a b ⊆ Icc (K.physicalLeft i) (K.physicalRight i) := by
    rintro r ⟨y, hy, rfl⟩
    exact P.mapsTo (hsub hy)
  rw [P.reciprocal_mass_change hT hS h hi hab hsub,
    intervalIntegral.integral_of_le (h.2.2.2.2.2.2.2.1 i).1.le,
    ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_mono_set hcont.integrableOn_Icc hnonneg himage.eventuallySubset

/-- The determinant identity uses the actual physical profile at the
genuine inverse point.  Its sign is independent of the chart orientation. -/
theorem N06ReferenceNegativeInverseData.reciprocalHeight_determinant
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (P : N06ReferenceNegativeInverseData C K i)
    {y : ℝ} (hy : y ∈ Icc (K.left i) (K.right i)) :
    y * P.reciprocalHeight y ^ 4 =
      -(D.w (P.inverse y) * (deriv D.w (P.inverse y) / P.inverse y)) := by
  have hd := n06_reference_negative_height_normalization hT hS h hi (P.mapsTo hy)
  have he := hd.2.2.2.2.2
  rw [P.right_inverse y hy] at he
  have hyEq : y = -(n06ReferenceNegativeH C K i (P.inverse y) ^ 4 *
      (D.w (P.inverse y) * (deriv D.w (P.inverse y) / P.inverse y))) := by
    linarith only [he]
  change y * (n06ReferenceNegativeH C K i (P.inverse y))⁻¹ ^ 4 = _
  nth_rw 1 [hyEq]
  field_simp [hd.2.2.1.ne']
  <;> ring

private theorem n06_scalar_fourth_root_upper
    {u y Q : ℝ} (hu : 0 ≤ u) (hy : 0 < y) (hQ : 0 ≤ Q)
    (hpower : y * u ^ 4 ≤ Q) : u ≤ (1 + Q) * (1 + y⁻¹) := by
  have hfour : u ^ 4 ≤ Q / y := (le_div_iff₀ hy).mpr (by simpa only [mul_comm] using hpower)
  have hself : u ≤ 1 + u ^ 4 := by
    by_cases hsmall : u ≤ 1
    · exact hsmall.trans (le_add_of_nonneg_right (pow_nonneg hu _))
    · exact (le_self_pow₀ (le_of_lt (lt_of_not_ge hsmall)) (by norm_num : (4 : ℕ) ≠ 0)).trans
        (le_add_of_nonneg_left zero_le_one)
  have hsum : u ≤ 1 + Q / y := by linarith only [hself, hfour]
  apply hsum.trans
  rw [div_eq_mul_inv]
  nlinarith only [hQ, (inv_pos.mpr hy).le]

/-- Global smooth physical-profile bounds give one actual polynomial
upper bound at every positive canonical radius on every negative piece. -/
theorem n06_referenceNegative_reciprocalHeight_upper
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i, K.positive i = false →
      ∀ P : N06ReferenceNegativeInverseData C K i,
      ∀ y ∈ Icc (K.left i) (K.right i), 0 < y →
        P.reciprocalHeight y ≤ M * (1 + y⁻¹) := by
  have hgeom : RadialProfileGeometry D := h.1.1.1.1.1.choose_spec.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  obtain ⟨B0, hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.continuous.continuousOn : ContinuousOn D.w (Icc D.a D.b))
  obtain ⟨B1, hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hw.continuous_deriv (by simp)).continuousOn :
      ContinuousOn (deriv D.w) (Icc D.a D.b))
  let B : ℝ := max 1 (max B0 B1)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  let Q : ℝ := B ^ 2 * D.a⁻¹
  have hQ : 0 ≤ Q := mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hgeom.1.le)
  refine ⟨1 + Q, le_add_of_nonneg_right hQ, fun i hi P y hy hypos => ?_⟩
  have hr := n06_negative_closed_core h hi (P.mapsTo hy)
  have hrpos : 0 < P.inverse y := hgeom.1.trans hr.1
  have hwB : |D.w (P.inverse y)| ≤ B := by
    have he : |D.w (P.inverse y)| ≤ B0 := by
      simpa only [Real.norm_eq_abs] using hB0 _ ⟨hr.1.le, hr.2.le⟩
    exact he.trans ((le_max_left B0 B1).trans (le_max_right _ _))
  have hdB : |deriv D.w (P.inverse y)| ≤ B := by
    have he : |deriv D.w (P.inverse y)| ≤ B1 := by
      simpa only [Real.norm_eq_abs] using hB1 _ ⟨hr.1.le, hr.2.le⟩
    exact he.trans ((le_max_right B0 B1).trans (le_max_right _ _))
  have hrinv : (P.inverse y)⁻¹ ≤ D.a⁻¹ := inv_anti₀ hgeom.1 hr.1.le
  have hproduct : -(D.w (P.inverse y) * (deriv D.w (P.inverse y) / P.inverse y)) ≤ Q := by
    calc
      _ ≤ |D.w (P.inverse y) * (deriv D.w (P.inverse y) / P.inverse y)| := neg_le_abs _
      _ = (|D.w (P.inverse y)| * |deriv D.w (P.inverse y)|) * (P.inverse y)⁻¹ := by
        rw [abs_mul, abs_div, abs_of_pos hrpos, div_eq_mul_inv]
        ring
      _ ≤ (B * B) * (P.inverse y)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul hwB hdB (abs_nonneg _) hB)
          (inv_nonneg.mpr hrpos.le)
      _ ≤ (B * B) * D.a⁻¹ := mul_le_mul_of_nonneg_left hrinv (mul_nonneg hB hB)
      _ = Q := by dsimp only [Q]; ring
  exact n06_scalar_fourth_root_upper
    (P.reciprocalHeight_regular hT hS h hi hy).2.le hypos hQ
    ((P.reciprocalHeight_determinant hT hS h hi hy).trans_le hproduct)

end ContinuousFlexibility.Statements
