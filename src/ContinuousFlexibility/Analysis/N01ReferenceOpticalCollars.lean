import ContinuousFlexibility.Analysis.OpticalTravelCollar
import ContinuousFlexibility.Analysis.N01ReturnMargins
import ContinuousFlexibility.Analysis.N01ControlCellBounds
import Mathlib.Topology.Order.OrderClosed

/-!
# Quantitative optical collars of the actual reference components

The inverse-profile jet bound controls the derivative of the squared
optical speed on each containing reference cell. The reference return
margin supplies a positive travel lower bound in the same cell weight.
The quantitative maximum argument then constructs an actual interior
collar. No preassigned middle third is used in this construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem opticalSquaredSpeed_deriv_bound_of_jets
    {w : ℝ → ℝ} {r K A : ℝ}
    (hw : DifferentiableAt ℝ w r) (hwd : DifferentiableAt ℝ (deriv w) r)
    (hr : r ≠ 0) (hwr : w r ≠ 0) (hK : 0 ≤ K)
    (hw₁ : |deriv w r| ≤ K) (hw₂ : |deriv (deriv w) r| ≤ K)
    (hr₁ : |r⁻¹| ≤ K) (hr₂ : |(r ^ 2)⁻¹| ≤ K)
    (hinv : |(w r)⁻¹| + |deriv (fun s => (w s)⁻¹) r| ≤ A) :
    |deriv (fun s => -deriv w s / (s * w s)) r| ≤ 3 * K ^ 2 * A := by
  have hri : HasDerivAt (fun s : ℝ => s⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  have hwi : DifferentiableAt ℝ (fun s => (w s)⁻¹) r := hw.inv hwr
  have hprod := (hwd.hasDerivAt.neg.mul hri).mul hwi.hasDerivAt
  have hQ := hprod.congr_of_eventuallyEq
    (f₁ := fun s => -deriv w s / (s * w s))
    (Eventually.of_forall fun s => by
      simp only [Pi.mul_apply, Pi.neg_apply, div_eq_mul_inv, mul_inv_rev]
      ring)
  have hder : deriv (fun s => -deriv w s / (s * w s)) r =
      (-deriv (deriv w) r) * r⁻¹ * (w r)⁻¹ +
      (-deriv w r) * (-(r ^ 2)⁻¹) * (w r)⁻¹ +
      (-deriv w r) * r⁻¹ * deriv (fun s => (w s)⁻¹) r := by
    rw [hQ.deriv]
    simp only [Pi.neg_apply, Pi.mul_apply]
    ring
  have hu : |(w r)⁻¹| ≤ A :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans hinv
  have hdu : |deriv (fun s => (w s)⁻¹) r| ≤ A :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans hinv
  have hthree {x y u : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K) (hu : |u| ≤ A) :
      |x * y * u| ≤ K ^ 2 * A := by
    rw [abs_mul, abs_mul, pow_two]
    exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) hK) hu
      (abs_nonneg _) (mul_nonneg hK hK)
  rw [hder]
  calc
    _ ≤ |(-deriv (deriv w) r) * r⁻¹ * (w r)⁻¹ +
          (-deriv w r) * (-(r ^ 2)⁻¹) * (w r)⁻¹| +
        |(-deriv w r) * r⁻¹ * deriv (fun s => (w s)⁻¹) r| := abs_add_le _ _
    _ ≤ (|(-deriv (deriv w) r) * r⁻¹ * (w r)⁻¹| +
          |(-deriv w r) * (-(r ^ 2)⁻¹) * (w r)⁻¹|) +
        |(-deriv w r) * r⁻¹ * deriv (fun s => (w s)⁻¹) r| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (K ^ 2 * A + K ^ 2 * A) + K ^ 2 * A :=
      add_le_add
        (add_le_add (hthree (by simpa only [abs_neg] using hw₂) hr₁ hu)
          (hthree (by simpa only [abs_neg] using hw₁)
            (by simpa only [abs_neg] using hr₂) hu))
        (hthree (by simpa only [abs_neg] using hw₁) hr₁ hdu)
    _ = _ := by ring

/-- One coefficient power controls the derivative of the actual squared
speed on every reference cell. -/
theorem IsAccumulatingProfile.opticalSquaredSpeed_deriv_cell_bound
    {D : ReferenceData} (hRef : IsAccumulatingProfile D) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ j r, r ∈ D.cells j →
      |deriv (fun s => -deriv D.w s / (s * D.w s)) r| ≤
        K * radialE (D.cellIndex j) ^ A := by
  obtain ⟨A, hA, hInv⟩ := hRef.inverse_first_jets_cell_bound
  obtain ⟨B, hdata⟩ := hRef
  have hgeom : RadialProfileGeometry D := hdata.1
  have hpart : RadialPartition D := hdata.2.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hw₁ : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hw₂ : ContDiff ℝ ∞ (deriv (deriv D.w)) := (contDiff_infty_iff_deriv.mp hw₁).2
  have hrnz (r : ℝ) (hr : r ∈ Icc D.a D.b) : r ≠ 0 := (hgeom.1.trans_le hr.1).ne'
  let F : ℝ → ℝ × ℝ × ℝ × ℝ := fun r =>
    (deriv D.w r, deriv (deriv D.w) r, r⁻¹, (r ^ 2)⁻¹)
  have hF : ContinuousOn F (Icc D.a D.b) :=
    hw₁.continuous.continuousOn.prodMk
      (hw₂.continuous.continuousOn.prodMk
        ((continuousOn_id.inv₀ hrnz).prodMk
          ((continuousOn_id.pow 2).inv₀ (fun r hr => pow_ne_zero 2 (hrnz r hr)))))
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  let B₁ : ℝ := max B₀ 1
  have hB₁ : 0 < B₁ := zero_lt_one.trans_le (le_max_right _ _)
  have hFb (r : ℝ) (hr : r ∈ Icc D.a D.b) :
      |deriv D.w r| ≤ B₁ ∧ |deriv (deriv D.w) r| ≤ B₁ ∧
        |r⁻¹| ≤ B₁ ∧ |(r ^ 2)⁻¹| ≤ B₁ := by
    have hb := (hB₀ r hr).trans (le_max_left B₀ 1)
    simpa only [F, Prod.norm_def, Real.norm_eq_abs, max_le_iff] using hb
  refine ⟨3 * B₁ ^ 2 * A, A, mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hB₁)) hA,
    hA, fun j r hr => ?_⟩
  have hrD := hpart.2.2.2.1 j hr
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hFb r ⟨hrD.1.le, hrD.2.le⟩
  have hb := opticalSquaredSpeed_deriv_bound_of_jets
    (hw.differentiable (by simp) r) (hw₁.differentiable (by simp) r)
    (hrnz r ⟨hrD.1.le, hrD.2.le⟩) (hgeom.2.2.2.2.1 r hrD).ne'
    hB₁.le h₁ h₂ h₃ h₄ (hInv j r hr)
  exact hb.trans_eq (by ring)

/-- The open-cell estimate extends to both actual turning radii. -/
theorem IsAccumulatingProfile.opticalSquaredSpeed_deriv_component_bound
    {D : ReferenceData} (hRef : IsAccumulatingProfile D) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ l h j,
      NegativeRadialComponent D l h → Ioo l h ⊆ D.cells j →
      ∀ r ∈ Icc l h,
        |deriv (fun s => -deriv D.w s / (s * D.w s)) r| ≤
          K * radialE (D.cellIndex j) ^ A := by
  obtain ⟨K, A, hK, hA, hb⟩ := hRef.opticalSquaredSpeed_deriv_cell_bound
  obtain ⟨B, hdata⟩ := hRef
  have hgeom : RadialProfileGeometry D := hdata.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hw₁ : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  let Q : ℝ → ℝ := fun s => -deriv D.w s / (s * D.w s)
  have hQ : ContDiffOn ℝ ∞ Q (Ioo D.a D.b) :=
    hw₁.neg.contDiffOn.div (contDiff_id.mul hw).contDiffOn
      (fun r hr => mul_ne_zero (hgeom.1.trans hr.1).ne' (hgeom.2.2.2.2.1 r hr).ne')
  have hQd : ContinuousOn (deriv Q) (Ioo D.a D.b) :=
    (hQ.deriv_of_isOpen isOpen_Ioo (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)).continuousOn
  refine ⟨K, A, hK, hA, fun l h j hcomp hj r hr => ?_⟩
  have hcl : closure (Ioo l h) = Icc l h := closure_Ioo hcomp.2.1.ne
  apply le_on_closure (fun t ht => hb j t (hj ht))
  · rw [hcl]
    exact hQd.abs.mono (fun t ht => ⟨hcomp.1.trans_le ht.1, ht.2.trans_lt hcomp.2.2.1⟩)
  · exact continuousOn_const
  · rwa [hcl]

/-- The collar is selected from the actual profile and actual negative
components, with every width and speed loss expressed in one containing
reference-cell weight. -/
theorem N01Properties.reference_opticalCollars
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε) :
    ∃ K A B : ℝ, 0 < K ∧ 0 < A ∧ 0 < B ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧ ∃ x : ℝ,
      let τ := radialE (D.cellIndex j) ^ (-B)
      let δ := (τ / (C.right m - C.left m)) ^ 2 /
        (4 * (K * radialE (D.cellIndex j) ^ A + 1))
      0 < δ ∧ C.left m < x - δ ∧ x + δ < C.right m ∧
      ∀ r ∈ Icc (x - δ) (x + δ),
        τ / (2 * (C.right m - C.left m)) ≤ opticalSpeed D.w r := by
  obtain ⟨K, A, hK, hA, hbound⟩ :=
    hN01.1.1.opticalSquaredSpeed_deriv_component_bound
  obtain ⟨B, hB, hmargin⟩ := n01Properties_returnMargins hN01
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  obtain ⟨B₀, hdata⟩ := hN01.1.1
  have hgeom : RadialProfileGeometry D := hdata.1
  refine ⟨K, A, B, hK, hA, hB, fun m => ?_⟩
  obtain ⟨_, j, hj, c, hc, hcinv, hsine⟩ := hmargin m
  have hcomp := n01Properties_negativeRadialComponent hN01 m
  have htravel : 0 ≤ C.travel m := by
    rw [controlGeometry_travel_eq_radialTravel hC m]
    exact intervalIntegral.integral_nonneg_of_forall hcomp.2.1.le (fun _ => Real.sqrt_nonneg _)
  have hcTravel : c ≤ C.travel m := by
    have hs := hsine 1 (by omega)
    simp only [Nat.cast_one, one_mul, div_one] at hs
    exact hs.trans (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg htravel))
  have hEpos : 0 < radialE (D.cellIndex j) := Real.exp_pos _
  have hpowpos : 0 < radialE (D.cellIndex j) ^ B := Real.rpow_pos_of_pos hEpos _
  have hτc : radialE (D.cellIndex j) ^ (-B) ≤ c := by
    rw [Real.rpow_neg hEpos.le]
    exact (inv_le_comm₀ hpowpos hc).mpr hcinv
  have hτ : 0 < radialE (D.cellIndex j) ^ (-B) := Real.rpow_pos_of_pos hEpos _
  have hτtravel : radialE (D.cellIndex j) ^ (-B) ≤
      opticalTravel D.w (C.left m) (C.right m) := by
    have heq : C.travel m = opticalTravel D.w (C.left m) (C.right m) :=
      controlGeometry_travel_eq_radialTravel hC m
    rw [← heq]
    exact hτc.trans hcTravel
  have hwpos : ∀ r ∈ Icc (C.left m) (C.right m), 0 < D.w r :=
    fun r hr => hgeom.2.2.2.2.1 r
      ⟨hcomp.1.trans_le hr.1, hr.2.trans_lt hcomp.2.2.1⟩
  obtain ⟨x, hx⟩ := exists_opticalSpeed_quantitative_collar
    (hgeom.1.trans hcomp.1) hcomp.2.1 hgeom.2.2.1.1 hwpos
    hcomp.2.2.2.1 hcomp.2.2.2.2.1
    (mul_nonneg hK.le (Real.rpow_nonneg hEpos.le _))
    (hbound _ _ j hcomp hj) hτ hτtravel
  exact ⟨j, hj, x, hx⟩

end ContinuousFlexibility.Statements
