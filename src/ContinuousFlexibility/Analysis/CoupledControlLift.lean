module

public import ContinuousFlexibility.Analysis.CoupledCircleMultiplier
public import ContinuousFlexibility.Analysis.CoupledControlAlgebra

/-!
# Recovery of smooth controls from the actual circle space

A reciprocal diagonal followed by angular averaging gives a constant circle
element at every weighted order.  Its restriction is the original Banach
diagonal inverse applied to the original weighted mean.  This recovers
regular controls from the fixed-point identity without asserting that every
element of the base control space has all weighted orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped NNReal

theorem coupled_angularMean_const (c : ℝ) :
    angularMean (fun _ : ℝ => c) = c := by
  rw [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_div]
  exact inv_mul_cancel_left₀ Real.pi_ne_zero c

theorem coupled_angularMean_eq_of_constant (f : ℝ → ℝ)
    (hf : ∀ θ φ, f θ = f φ) (θ : ℝ) : angularMean f = f θ := by
  calc
    angularMean f = angularMean (fun _ : ℝ => f θ) :=
      congrArg angularMean (funext (fun φ => hf φ θ))
    _ = f θ := coupled_angularMean_const _

theorem coupled_inverseDiagonal_bound (a : ℕ → ℝ)
    (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (m : ℕ) : |(a m)⁻¹| ≤ 2 := by
  calc
    |(a m)⁻¹| = 1 / |a m| := by rw [abs_inv, one_div]
    _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) (ha m)
    _ = 2 := by norm_num

section CircleModel

variable {T : MaterialData} {γ : ℝ} {M : CircleModelData}

/-- The unique actual circle element with reciprocal-diagonal constant
components.  The lower diagonal bound is the one supplied by N08. -/
def coupledInverseControlLift (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) : M.Space →L[ℝ] M.Space :=
  (coupledCircleMultiplier hM (fun m => (a m)⁻¹) 2
    (coupled_inverseDiagonal_bound a ha)).comp (circleAngularMeanProjection hM)

theorem coupledInverseControlLift_apply (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (u : M.Space) :
    coupledInverseControlLift hM a ha u =
      coupledCircleMultiplier hM (fun m => (a m)⁻¹) 2
        (coupled_inverseDiagonal_bound a ha) (circleAngularMeanProjection hM u) :=
  ContinuousLinearMap.comp_apply _ _ u

theorem coupledInverseControlLift_decode (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|)
    (u : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledInverseControlLift hM a ha u) m θ =
      (a m)⁻¹ * angularMean (M.decode u m) := by
  exact (congrArg (fun v : M.Space => M.decode v m θ)
    (coupledInverseControlLift_apply hM a ha u)).trans
      ((coupledCircleMultiplier_decode hM (fun m => (a m)⁻¹) 2
        (coupled_inverseDiagonal_bound a ha) (circleAngularMeanProjection hM u) m θ).trans
          (congrArg ((a m)⁻¹ * ·) (circleAngularMeanProjection_decode hM u m θ)))

theorem coupledInverseControlLift_constant (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|)
    (u : M.Space) (m : ℕ) (θ φ : ℝ) :
    M.decode (coupledInverseControlLift hM a ha u) m θ =
      M.decode (coupledInverseControlLift hM a ha u) m φ := by
  exact (coupledInverseControlLift_decode hM a ha u m θ).trans
    (coupledInverseControlLift_decode hM a ha u m φ).symm

theorem coupledInverseControlLift_even (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (u : M.Space) (m : ℕ) :
    Function.Even (M.decode (coupledInverseControlLift hM a ha u) m) :=
  fun θ => coupledInverseControlLift_constant hM a ha u m (-θ) θ

/-- The same factor two bounds every weighted circle seminorm. -/
theorem coupledInverseControlLift_grading_le (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) (n : ℕ) (u : M.Space) :
    M.grading n (coupledInverseControlLift hM a ha u) ≤ 2 * M.grading n u := by
  calc
    _ = M.grading n (coupledCircleMultiplier hM (fun m => (a m)⁻¹) 2
        (coupled_inverseDiagonal_bound a ha) (circleAngularMeanProjection hM u)) :=
      congrArg (M.grading n) (coupledInverseControlLift_apply hM a ha u)
    _ = M.grading n (coupledCircleMultiplierLinear hM (fun m => (a m)⁻¹) 2
        (coupled_inverseDiagonal_bound a ha) (circleAngularMeanProjection hM u)) := rfl
    _ ≤ 2 * M.grading n (circleAngularMeanProjection hM u) := by
      simpa only [NNReal.coe_ofNat] using
        coupledCircleMultiplierLinear_grading_le hM (fun m => (a m)⁻¹) 2
          (coupled_inverseDiagonal_bound a ha) n (circleAngularMeanProjection hM u)
    _ ≤ 2 * M.grading n u := mul_le_mul_of_nonneg_left
      (circleAngularMeanLinear_grading_le hM n u) (by norm_num)

theorem coupledInverseControlLift_isTame (hM : IsCircleModel T γ M)
    (a : ℕ → ℝ) (ha : ∀ m, (1 / 2 : ℝ) ≤ |a m|) :
    ContinuousFlexibility.Analysis.IsTameLinear M.grading M.grading
      (coupledInverseControlLift hM a ha).toLinearMap 0 0 := by
  intro n _
  exact ⟨2, fun u => by simpa only [Nat.add_zero, NNReal.coe_ofNat,
    ContinuousLinearMap.coe_coe] using
    coupledInverseControlLift_grading_le hM a ha n u⟩

end CircleModel

section ControlRestriction

variable {T : MaterialData} {S : PhysicalSpacesData}

/-- Recovery agrees with the already chosen Banach inverse, including the
same material normalization in the restriction. -/
theorem coupledInverseControlLift_restriction
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
    (hJ : ∀ u, B.J z (B.JInverse z u) = u)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) (u : CircleSpace S) :
    B.restriction (coupledInverseControlLift hS (B.diagonal z) hlo u) =
      B.JInverse z (B.restriction u) := by
  apply lp.ext
  funext m
  have heq : (S.circle (3 / 4 : ℝ)).decode
      (coupledInverseControlLift hS (B.diagonal z) hlo u) m =
      (fun _ : ℝ => (B.diagonal z m)⁻¹ *
        angularMean ((S.circle (3 / 4 : ℝ)).decode u m)) :=
    funext (coupledInverseControlLift_decode hS (B.diagonal z) hlo u m)
  have hmean := (congrArg angularMean heq).trans (coupled_angularMean_const _)
  calc
    _ = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
        angularMean ((S.circle (3 / 4 : ℝ)).decode
          (coupledInverseControlLift hS (B.diagonal z) hlo u) m) := hrestriction _ m
    _ = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
        ((B.diagonal z m)⁻¹ * angularMean ((S.circle (3 / 4 : ℝ)).decode u m)) :=
      congrArg (T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * ·) hmean
    _ = (B.diagonal z m)⁻¹ * (T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
        angularMean ((S.circle (3 / 4 : ℝ)).decode u m)) := mul_left_comm _ _ _
    _ = (B.diagonal z m)⁻¹ * B.restriction u m :=
      congrArg ((B.diagonal z m)⁻¹ * ·) (hrestriction u m).symm
    _ = B.JInverse z (B.restriction u) m :=
      (controlJInverse_apply_of_diagonal B z hdiag hJ hlo (B.restriction u) m).symm

theorem controlRestriction_eq_zero_iff
    (B : ControlColumnData S)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hH : ∀ m, 0 < T.H (T.sample m)) (u : CircleSpace S) :
    B.restriction u = 0 ↔
      ∀ m, angularMean ((S.circle (3 / 4 : ℝ)).decode u m) = 0 := by
  constructor
  · exact fun hu m => controlRestriction_mean_zero B hrestriction hH hu m
  · intro hu
    apply lp.ext
    funext m
    rw [hrestriction, hu m, mul_zero]
    simp only [lp.coeFn_zero, Pi.zero_apply]

/-- The weighted mean map loses no information on constant controls. -/
theorem controlRestriction_injective_on_constants
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hH : ∀ m, 0 < T.H (T.sample m)) {u v : CircleSpace S}
    (hu : ∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode u m θ =
      (S.circle (3 / 4 : ℝ)).decode u m φ)
    (hv : ∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode v m θ =
      (S.circle (3 / 4 : ℝ)).decode v m φ)
    (heq : B.restriction u = B.restriction v) : u = v := by
  apply hS.2.2.2.2.2.1
  funext m θ
  have hcoord := congrArg (fun ξ : ControlBanach => ξ m) heq
  rw [hrestriction, hrestriction] at hcoord
  have hmean := mul_left_cancel₀ (Real.rpow_pos_of_pos (hH m) _).ne' hcoord
  exact (coupled_angularMean_eq_of_constant _ (hu m) θ).symm.trans
    (hmean.trans (coupled_angularMean_eq_of_constant _ (hv m) θ))

/-- A control represented by a diagonal inverse of a circle mean has an
actual constant-circle realization, with all orders bounded at once. -/
theorem exists_constant_control_of_inverse_restriction
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (z : AnnularState S × ℝ)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
    (hJ : ∀ u, B.J z (B.JInverse z u) = u)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
    (u : CircleSpace S) (ξ : ControlBanach) (hξ : ξ = B.JInverse z (B.restriction u)) :
    ∃ κ : CircleSpace S,
      (∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode κ m θ =
        (S.circle (3 / 4 : ℝ)).decode κ m φ) ∧
      B.restriction κ = ξ ∧
      ∀ n, (S.circle (3 / 4 : ℝ)).grading n κ ≤
        2 * (S.circle (3 / 4 : ℝ)).grading n u := by
  refine ⟨coupledInverseControlLift hS (B.diagonal z) hlo u,
    coupledInverseControlLift_constant hS (B.diagonal z) hlo u, ?_,
    fun n => coupledInverseControlLift_grading_le hS (B.diagonal z) hlo n u⟩
  exact (coupledInverseControlLift_restriction hS B z hrestriction hdiag hJ hlo u).trans hξ.symm

end ControlRestriction

end ContinuousFlexibility.Statements
