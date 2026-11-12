import ContinuousFlexibility.Analysis.N06ReferenceNegativeHeight

/-!
# The actual selected reference chart satisfies the scalar Airy equation

The closed forward-symbol identities force the Airy equation for the old
negative chart itself.  Differentiation within its true closed physical
interval fixes its root slope, including its sign.  These identities do
not identify an independently constructed positive extension with an
arbitrary old positive chart.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n06_scalar_airy_from_normalization
    {H w y s d r : ℝ} (hw : w ≠ 0) (hr : r ≠ 0)
    (hnormal : H ^ 2 * w * |s| = 1)
    (hdet : H ^ 4 * (w * (d / r)) = -y) :
    y * s ^ 2 = -d / (r * w) := by
  have hnormal2 : H ^ 4 * w ^ 2 * s ^ 2 = 1 := by
    have he := congrArg (fun x : ℝ => x ^ 2) hnormal
    simpa only [mul_pow, ← pow_mul, sq_abs, one_pow] using he
  have hy : y = -(H ^ 4 * (w * (d / r))) := by linarith only [hdet]
  rw [hy]
  calc
    -(H ^ 4 * (w * (d / r))) * s ^ 2 =
        (-d / (r * w)) * (H ^ 4 * w ^ 2 * s ^ 2) := by
      field_simp [hr, hw]
      <;> ring
    _ = -d / (r * w) := by rw [hnormal2, mul_one]

private theorem n06_scalar_airy_root_slope
    {w Y : ℝ → ℝ} {a b r : ℝ} (hab : a < b) (hr : r ∈ Icc a b)
    (hrpos : 0 < r) (hwpos : 0 < w r) (hw : ContDiff ℝ ∞ w)
    (hY : ContDiffAt ℝ ∞ Y r) (hzero : Y r = 0) (hroot : deriv w r = 0)
    (hidentity : ∀ s ∈ Icc a b,
      Y s * deriv Y s ^ 2 = -deriv w s / (s * w s)) :
    deriv Y r ^ 3 = -deriv (deriv w) r / (r * w r) := by
  have hdY := (hY.differentiableAt (by simp)).hasDerivAt
  have hdYd := ((hY.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hLraw := hdY.fun_mul (hdYd.pow 2)
  have hL : HasDerivAt (fun s => Y s * deriv Y s ^ 2) (deriv Y r ^ 3) r := by
    convert hLraw using 1
    <;> simp only [Pi.pow_apply, hzero, zero_mul, add_zero]
    <;> ring
  have hdw := (hw.differentiable (by simp) r).hasDerivAt
  have hdwd := ((contDiff_infty_iff_deriv.mp hw).2.differentiable (by simp) r).hasDerivAt
  have hRraw := hdwd.neg.fun_div ((hasDerivAt_id r).fun_mul hdw)
    (mul_ne_zero hrpos.ne' hwpos.ne')
  have hR : HasDerivAt (fun s => -deriv w s / (s * w s))
      (-deriv (deriv w) r / (r * w r)) r := by
    convert hRraw using 1
    <;> simp only [Pi.neg_apply, id_eq, hroot, neg_zero, zero_mul, sub_zero]
    <;> field_simp [hrpos.ne', hwpos.ne']
    <;> ring
  have hRw := hR.hasDerivWithinAt.congr_of_mem hidentity hr
  exact (hL.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab r hr)).symm.trans
    (hRw.derivWithin (uniqueDiffOn_Icc hab r hr))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- The actual old negative coordinate satisfies the normalized scalar
Airy equation at every point of its true closed physical half. -/
theorem n06_reference_negative_airy_identity
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
    n06ReferenceNegativeY C K i r * deriv (n06ReferenceNegativeY C K i) r ^ 2 =
      -deriv D.w r / (r * D.w r) := by
  have hgeom : RadialProfileGeometry D := h.1.1.1.1.1.choose_spec.1
  obtain ⟨m, hm⟩ := n06_negativePiece_is_cutHalf h.2.2.2.2 h.1.1.1.2.2.2.1 hi
  have hcore := n06_cutPiece_closed_subset h m hm hr
  have hnorm := n06_reference_negative_height_normalization hT hS h hi hr
  exact n06_scalar_airy_from_normalization
    (hgeom.2.2.2.2.1 r hcore).ne' (hgeom.1.trans hcore.1).ne'
    hnorm.2.2.2.2.1 hnorm.2.2.2.2.2

/-- The sign and scale of the selected forward root derivative are
fixed by the original physical curvature, with no new chart assumption. -/
theorem n06_reference_negative_root_slope_cube
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hroot : deriv D.w r = 0) :
    deriv (n06ReferenceNegativeY C K i) r ^ 3 =
      -deriv (deriv D.w) r / (r * D.w r) := by
  have hgeom : RadialProfileGeometry D := h.1.1.1.1.1.choose_spec.1
  obtain ⟨m, hm⟩ := n06_negativePiece_is_cutHalf h.2.2.2.2 h.1.1.1.2.2.2.1 hi
  have hcore := n06_cutPiece_closed_subset h m hm hr
  have hY := (n06_reference_negative_height_normalization hT hS h hi hr).1
  have hYzero : n06ReferenceNegativeY C K i r = 0 :=
    n05_negative_reference_root_image hT hS h hi (x := (r, 0)) hr hroot
  exact n06_scalar_airy_root_slope (h.2.2.2.2.1.referenceBounds i).1 hr
    (hgeom.1.trans hcore.1) (hgeom.2.2.2.2.1 r hcore) hgeom.2.2.1.1 hY hYzero hroot
    (fun s hs => n06_reference_negative_airy_identity hT hS h hi hs)

theorem n06_reference_negative_root_abs_slope_cube
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hroot : deriv D.w r = 0) :
    |deriv (n06ReferenceNegativeY C K i) r| ^ 3 =
      |deriv (deriv D.w) r| / (r * D.w r) := by
  have hgeom : RadialProfileGeometry D := h.1.1.1.1.1.choose_spec.1
  obtain ⟨m, hm⟩ := n06_negativePiece_is_cutHalf h.2.2.2.2 h.1.1.1.2.2.2.1 hi
  have hcore := n06_cutPiece_closed_subset h m hm hr
  rw [← abs_pow, n06_reference_negative_root_slope_cube hT hS h hi hr hroot,
    abs_div, abs_neg, abs_mul, abs_of_pos (hgeom.1.trans hcore.1),
    abs_of_pos (hgeom.2.2.2.2.1 r hcore)]

end ContinuousFlexibility.Statements
