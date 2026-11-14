module

public import ContinuousFlexibility.Analysis.N06ReferenceNegativeRigidity
public import ContinuousFlexibility.Analysis.N06RadialReferenceGeometry
public import ContinuousFlexibility.Analysis.N05N06ClosedChartBridge

/-!
# The actual negative reference height and root curvature

The selected negative reference chart is radial on its closed physical
piece.  Its actual Frechet Jacobian and principal symbol force the
Liouville normalization `H^2 w |Y'| = 1`.  Differentiating the genuine
determinant identity at a physical root then identifies the original
root curvature with the sixth power of the reciprocal height.

All endpoint derivatives come from the smooth forward chart and
uniqueness of derivatives within the closed physical interval.  No
boundary value of the totalized inverse chart is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n06ReferenceNegativeY {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S) (i : ℕ) (r : ℝ) : ℝ :=
  (K.chart (C.referenceState, 0) i (r, 0)).1

def n06ReferenceNegativeH {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S) (i : ℕ) (r : ℝ) : ℝ :=
  K.height (C.referenceState, 0) i (r, 0)

private theorem n06_closed_radial_chart_partials
    {F : PolarPoint → PolarPoint} {a b r : ℝ} (hab : a < b)
    (hr : r ∈ Icc a b) (hF : DifferentiableAt ℝ F (r, 0))
    (hshape : ∀ s ∈ Icc a b, ∀ θ, F (s, θ) = ((F (s, 0)).1, θ)) :
    radialPartial (fun p => (F p).1) (r, 0) = deriv (fun s => (F (s, 0)).1) r ∧
      angularPartial (fun p => (F p).1) (r, 0) = 0 ∧
      radialPartial (fun p => (F p).2) (r, 0) = 0 ∧
      angularPartial (fun p => (F p).2) (r, 0) = 1 ∧
      planeJacobian F (r, 0) = deriv (fun s => (F (s, 0)).1) r := by
  have hyr := (Radial.hasDerivAt_radialSlice hF.fst).deriv.symm
  have hyt : angularPartial (fun p => (F p).1) (r, 0) = 0 := by
    have heq : (fun θ => (F (r, θ)).1) = fun _ => (F (r, 0)).1 := by
      funext θ
      have he := congrArg (fun p : PolarPoint => p.1) (hshape r hr θ)
      simpa only using he
    have hzero : HasDerivAt (fun θ => (F (r, θ)).1) 0 0 := by
      rw [heq]
      exact hasDerivAt_const _ _
    exact (Radial.hasDerivAt_angularSlice hF.fst).unique hzero
  have htr : radialPartial (fun p => (F p).2) (r, 0) = 0 := by
    have hzero : HasDerivWithinAt (fun s => (F (s, 0)).2) 0 (Icc a b) r :=
      (hasDerivAt_const r (0 : ℝ)).hasDerivWithinAt.congr_of_mem
        (fun s hs => congrArg Prod.snd (hshape s hs 0)) hr
    have hu := uniqueDiffOn_Icc hab r hr
    exact ((Radial.hasDerivAt_radialSlice hF.snd).hasDerivWithinAt.derivWithin hu).symm.trans
      (hzero.derivWithin hu)
  have htt : angularPartial (fun p => (F p).2) (r, 0) = 1 := by
    have heq : (fun θ => (F (r, θ)).2) = fun θ => θ :=
      funext fun θ => congrArg Prod.snd (hshape r hr θ)
    have hone : HasDerivAt (fun θ => (F (r, θ)).2) 1 0 := by
      rw [heq]
      exact hasDerivAt_id _
    exact (Radial.hasDerivAt_angularSlice hF.snd).unique hone
  refine ⟨hyr, hyt, htr, htt, ?_⟩
  rw [n05_planeJacobian_eq_partials hF, hyr, hyt, htr, htt]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- The original selected negative chart satisfies its exact radial
normalization and determinant formulas throughout the closed piece. -/
theorem n06_reference_negative_height_normalization
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
    ContDiffAt ℝ ∞ (n06ReferenceNegativeY C K i) r ∧
      ContDiffAt ℝ ∞ (n06ReferenceNegativeH C K i) r ∧
      0 < n06ReferenceNegativeH C K i r ∧
      deriv (n06ReferenceNegativeY C K i) r ≠ 0 ∧
      n06ReferenceNegativeH C K i r ^ 2 * D.w r *
        |deriv (n06ReferenceNegativeY C K i) r| = 1 ∧
      n06ReferenceNegativeH C K i r ^ 4 * (D.w r * (deriv D.w r / r)) =
        -n06ReferenceNegativeY C K i r := by
  let F : PolarPoint → PolarPoint := K.chart (C.referenceState, 0) i
  let Y : ℝ → ℝ := n06ReferenceNegativeY C K i
  let H : ℝ → ℝ := n06ReferenceNegativeH C K i
  change ContDiffAt ℝ ∞ Y r ∧ ContDiffAt ℝ ∞ H r ∧ 0 < H r ∧
    deriv Y r ≠ 0 ∧ H r ^ 2 * D.w r * |deriv Y r| = 1 ∧
      H r ^ 4 * (D.w r * (deriv D.w r / r)) = -Y r
  have h01 := h.1.1.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hpieces := h.2.2.2.2.1.1.referenceBounds
  have hreg := n05_reference_boundary_regular h.2.2.2.2.1.1 hz hs i (p := (r, 0)) hr
  have hline : ContDiffAt ℝ ∞ (fun s : ℝ => (s, (0 : ℝ))) r :=
    contDiffAt_id.prodMk contDiffAt_const
  have hY : ContDiffAt ℝ ∞ Y r := by
    have he : Y = (fun s : ℝ => (K.chart (C.referenceState, 0) i (s, 0)).1) := rfl
    rw [he]
    simpa only [Function.comp_def] using hreg.1.fst.comp r hline
  have hH : ContDiffAt ℝ ∞ H r := by
    have he : H = (fun s : ℝ => K.height (C.referenceState, 0) i (s, 0)) := rfl
    rw [he]
    simpa only [Function.comp_def] using hreg.2.1.comp r hline
  have hshape : ∀ s ∈ Icc (K.physicalLeft i) (K.physicalRight i), ∀ θ,
      F (s, θ) = ((F (s, 0)).1, θ) :=
    fun s hs θ => (n06_reference_negative_radial hT hS h hi s hs θ).1
  have hc := n06_closed_radial_chart_partials (F := F) (hpieces i).1 hr
    (hreg.1.differentiableAt (by simp)) hshape
  have hyr : radialPartial (fun p => (F p).1) (r, 0) = deriv Y r := hc.1
  have hyt : angularPartial (fun p => (F p).1) (r, 0) = 0 := hc.2.1
  have hJ : planeJacobian F (r, 0) = deriv Y r := hc.2.2.2.2
  have hYne : deriv Y r ≠ 0 := by
    rw [← hJ]
    exact hreg.2.2.1
  have hprincipal := (n05_negative_reference_symbol_closed hT hS h hi (x := (r, 0)) hr).1
  change H r ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D)
    (fun p => (F p).1) (fun p => (F p).1) (r, 0) = |planeJacobian F (r, 0)| at hprincipal
  simp only [n05PrincipalPair, n05RadialReferenceCoefficients, hyr, hyt,
    hJ, mul_zero, zero_mul, add_zero] at hprincipal
  change H r ^ 2 * (D.w r * deriv Y r * deriv Y r) = |deriv Y r| at hprincipal
  have hnormal : H r ^ 2 * D.w r * |deriv Y r| = 1 := by
    apply mul_right_cancel₀ (abs_ne_zero.mpr hYne)
    calc
      (H r ^ 2 * D.w r * |deriv Y r|) * |deriv Y r| =
          H r ^ 2 * D.w r * |deriv Y r| ^ 2 := by ring
      _ = H r ^ 2 * D.w r * (deriv Y r) ^ 2 := by rw [sq_abs]
      _ = |deriv Y r| := by nlinarith only [hprincipal]
      _ = 1 * |deriv Y r| := (one_mul _).symm
  exact ⟨hY, hH, hreg.2.2.2, hYne, hnormal,
    n05_negative_reference_determinant_closed hT hS h hi (x := (r, 0)) hr⟩

private theorem n06_closed_root_curvature_identity
    {w H Y : ℝ → ℝ} {a b r : ℝ} (hab : a < b) (hr : r ∈ Icc a b)
    (hrpos : 0 < r) (hw : ContDiff ℝ ∞ w)
    (hH : ContDiffAt ℝ ∞ H r) (hY : ContDiffAt ℝ ∞ Y r)
    (hwp : 0 < w r) (hHp : 0 < H r) (hroot : deriv w r = 0)
    (hnormal : H r ^ 2 * w r * |deriv Y r| = 1)
    (hidentity : ∀ s ∈ Icc a b, H s ^ 4 * (w s * (deriv w s / s)) = -Y s) :
    |deriv (deriv w) r| * H r ^ 6 * w r ^ 2 = r := by
  have hdw := (hw.differentiable (by simp) r).hasDerivAt
  have hdw' := ((contDiff_infty_iff_deriv.mp hw).2.differentiable (by simp) r).hasDerivAt
  have hdH := (hH.differentiableAt (by simp)).hasDerivAt
  have hd := (hdH.pow 4).fun_mul (hdw.fun_mul (hdw'.div (hasDerivAt_id r) hrpos.ne'))
  have hdG : HasDerivAt (fun s => H s ^ 4 * (w s * (deriv w s / s)))
      (H r ^ 4 * (w r * deriv (deriv w) r / r)) r := by
    convert hd using 1
    · funext s
      simp only [Pi.pow_apply, Pi.div_apply, id_eq]
    · simp only [Pi.pow_apply, Pi.div_apply, id_eq, hroot, zero_div, mul_zero,
        zero_mul, zero_add, sub_zero]
      field_simp [hrpos.ne']
      <;> ring
  have hdY := ((hY.differentiableAt (by simp)).hasDerivAt.neg).hasDerivWithinAt.congr_of_mem
    hidentity hr
  have hderiv : H r ^ 4 * (w r * deriv (deriv w) r / r) = -deriv Y r :=
    (hdG.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab r hr)).symm.trans
      (hdY.derivWithin (uniqueDiffOn_Icc hab r hr))
  have habs := congrArg abs hderiv
  simp only [abs_mul, abs_div, abs_pow, abs_of_pos hHp, abs_of_pos hwp,
    abs_of_pos hrpos, abs_neg] at habs
  have habs' : H r ^ 4 * w r * |deriv (deriv w) r| = |deriv Y r| * r := by
    apply (div_eq_iff hrpos.ne').mp
    simpa only [mul_div_assoc, mul_assoc] using habs
  calc
    |deriv (deriv w) r| * H r ^ 6 * w r ^ 2 =
        (H r ^ 4 * w r * |deriv (deriv w) r|) * (H r ^ 2 * w r) := by ring
    _ = (|deriv Y r| * r) * (H r ^ 2 * w r) := by rw [habs']
    _ = r * (H r ^ 2 * w r * |deriv Y r|) := by ring
    _ = r := by rw [hnormal, mul_one]

/-- The original physical root curvature is fixed by the actual
reference height; the formula holds at either end of either negative half. -/
theorem n06_reference_negative_root_curvature
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hroot : deriv D.w r = 0) :
    |deriv (deriv D.w) r| * n06ReferenceNegativeH C K i r ^ 6 * D.w r ^ 2 = r := by
  have h01 := h.1.1.1
  have hgeom : RadialProfileGeometry D := h01.1.1.choose_spec.1
  obtain ⟨m, hm⟩ := n06_negativePiece_is_cutHalf h.2.2.2.2.1 h01.2.2.2.1 hi
  have hcore : r ∈ radialCore D := n06_cutPiece_closed_subset h m hm hr
  have hdata := n06_reference_negative_height_normalization hT hS h hi hr
  exact n06_closed_root_curvature_identity (h.2.2.2.2.1.1.referenceBounds i).1 hr
    (hgeom.1.trans hcore.1) hgeom.2.2.1.1 hdata.2.1 hdata.1
    (hgeom.2.2.2.2.1 r hcore) hdata.2.2.1 hroot hdata.2.2.2.2.1
    (fun s hs => (n06_reference_negative_height_normalization hT hS h hi hs).2.2.2.2.2)

end ContinuousFlexibility.Statements
