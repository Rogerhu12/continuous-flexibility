module

public import ContinuousFlexibility.Analysis.ReturnChartUniformBounds

/-!
# Height-weight decay of the independent residual correction

The inverse transport has derivative at most six on the actual common
neighborhood. Its removable divided difference therefore has the same
bound, including at zero residual. The displacement and velocity maps
retain exactly the height weight of the independent decoded residual.
No nonzero-residual division or replacement residual space is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

theorem dslope_add_abs_le_of_deriv_bound
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {A : ℝ}
    (hA : ∀ x, |deriv G x| ≤ A) (x d : ℝ) :
    |dslope G x (x + d)| ≤ A := by
  rw [ContinuousFlexibility.Statements.returnCorrection_dslope_integral hG x d]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t => deriv G (x + t * d))
    (fun t _ => by simpa only [Real.norm_eq_abs] using hA (x + t * d))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

theorem reflected_drift_speed_abs_bound
    (v : ℝ → ℝ) {B : ℝ} (hv : ∀ θ, |v θ| ≤ B) (θ : ℝ) :
    |(v θ - v (-θ)) / 2| ≤ B ∧ |(-v (-θ) - v θ) / 2| ≤ B := by
  constructor
  · rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have h : |v θ - v (-θ)| ≤ |v θ| + |v (-θ)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (v θ) (-v (-θ))
    exact h.trans ((add_le_add (hv θ) (hv (-θ))).trans_eq (by ring))
  · rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have h : |-v (-θ) - v θ| ≤ |v (-θ)| + |v θ| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (-v (-θ)) (-v θ)
    exact h.trans ((add_le_add (hv (-θ)) (hv θ)).trans_eq (by ring))

theorem weighted_velocity_abs_le
    (d c v C P H : ℝ) (hd : |d| ≤ 3 / 2)
    (hv : |v| ≤ (12 * C * P) * H) :
    |d * c * v| ≤ (18 * C * P) * |c| * H := by
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_right hd (abs_nonneg c)) hv (abs_nonneg v)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) (abs_nonneg c))
  calc
    _ = |d| * |c| * |v| := by rw [abs_mul, abs_mul]
    _ ≤ ((3 / 2 : ℝ) * |c|) * ((12 * C * P) * H) := hb
    _ = _ := by ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

section Displacement

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (hflow : ∀ m θ, 1 / 2 ≤ deriv (C.minusFlow z m (C.right m)) θ ∧
    deriv (C.minusFlow z m (C.right m)) θ ≤ 3 / 2)

include hN hS hT hz hsector hflow

theorem N01Properties.returnCorrectionDisplacementLinear_weighted_abs_bound
    (ρ : CircleSpace S) (m : ℕ) (θ : ℝ) :
    |returnCorrectionDisplacementLinear S C z m θ ρ| ≤
      (12 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
        T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  let y := rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)
  let G : ℝ → ℝ := fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)
  have hG : ContDiff ℝ ∞ G := hN.returnTransportInverse_contDiff hS hT hz hsector m
  have hGb (t : ℝ) : |deriv G t| ≤ 6 := by
    have h := hN.returnTransportInverse_deriv_bounds hz hsector hflow m t
    rw [abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 6).trans h.1)]
    exact h.2
  have hquot := dslope_add_abs_le_of_deriv_bound (hG.of_le (by simp)) hGb y
    (returnResidualField S C z m y)
  have hH := (material_circle_sample_weights_pos hT hN.1.1).2
  have hρ : |(S.circle (3 / 4 : ℝ)).decode ρ m y| ≤
      (2 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
        T.H (T.sample m) ^ (3 / 4 : ℝ) := by
    simpa only [iteratedDeriv_zero, zero_add] using
      circleModel_iteratedDeriv_abs_le (hS.2.1 (3 / 4 : ℝ)) hH ρ m 0 y
  have hmul := mul_le_mul hquot hρ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
  calc
    _ = |dslope G y (y + returnResidualField S C z m y)| *
        |(S.circle (3 / 4 : ℝ)).decode ρ m y| := by
      rw [returnCorrectionDisplacementLinear_apply, abs_mul]
    _ ≤ 6 * ((2 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
        T.H (T.sample m) ^ (3 / 4 : ℝ)) := hmul
    _ = _ := by ring

end Displacement

section Velocity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (hflow : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
    1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2)

include hN hS hT hz hsector hflow

theorem N01Properties.returnCorrectionVelocityLinear_weighted_abs_bound
    (χ : ℕ → ℝ → ℝ) (ρ : CircleSpace S) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
    |returnCorrectionVelocityLinear D S C χ z m p ρ| ≤
      (18 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
        |deriv (χ m) p.1| * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hend (i : ℕ) (θ : ℝ) :
      1 / 2 ≤ deriv (C.minusFlow z i (C.right i)) θ ∧
        deriv (C.minusFlow z i (C.right i)) θ ≤ 3 / 2 :=
    hflow i (C.right i) ⟨(hcontrol.1 i).2.1.le, le_rfl⟩ θ
  let α := Function.invFun (C.minusFlow z m p.1) p.2
  let θ := Function.invFun
    (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m)) α
  have hd : |deriv (C.minusFlow z m p.1) α| ≤ 3 / 2 := by
    have h := hflow m p.1 hp α
    rw [abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans h.1)]
    exact h.2
  have hdisp := hN.returnCorrectionDisplacementLinear_weighted_abs_bound
    hS hT hz hsector hend ρ m θ
  have heq : returnCorrectionVelocityLinear D S C χ z m p ρ =
      deriv (C.minusFlow z m p.1) α * deriv (χ m) p.1 *
        returnCorrectionDisplacementLinear S C z m θ ρ :=
    returnCorrectionVelocityLinear_apply D S C χ z m p ρ
  exact (congrArg abs heq).trans_le
    (weighted_velocity_abs_le (deriv (C.minusFlow z m p.1) α) (deriv (χ m) p.1)
      (returnCorrectionDisplacementLinear S C z m θ ρ) circleSobolevConstant
      ((S.circle (3 / 4 : ℝ)).grading 1 ρ) (T.H (T.sample m) ^ (3 / 4 : ℝ)) hd hdisp)

theorem N01Properties.returnCorrectionDriftSpeedLinear_weighted_abs_bound
    (χ : ℕ → ℝ → ℝ) (ρ : CircleSpace S) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
    |returnCorrectionDriftLinear D S C χ z m p ρ| ≤
      (18 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
        |deriv (χ m) p.1| * T.H (T.sample m) ^ (3 / 4 : ℝ) ∧
    |returnCorrectionSpeedLinear D S C χ z m p ρ| ≤
      (18 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
        |deriv (χ m) p.1| * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have h := reflected_drift_speed_abs_bound
    (fun θ => returnCorrectionVelocityLinear D S C χ z m (p.1, θ) ρ)
    (B := (18 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
      |deriv (χ m) p.1| * T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun θ => hN.returnCorrectionVelocityLinear_weighted_abs_bound
      hS hT hz hsector hflow χ ρ m (p.1, θ) hp) p.2
  exact ⟨(congrArg abs (returnCorrectionDriftLinear_apply D S C χ z m p ρ)).trans_le h.1,
    (congrArg abs (returnCorrectionSpeedLinear_apply D S C χ z m p ρ)).trans_le h.2⟩

end Velocity

/-- A single actual N01 neighborhood retains the independent residual's
exact height exponent in the displacement, drift and speed correction. -/
theorem N01Properties.exists_weighted_independent_residual_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ∀ χ : ℕ → ℝ → ℝ, ∀ ρ : CircleSpace S, ∀ m p,
        p.1 ∈ Icc (C.left m) (C.right m) →
        |returnCorrectionDriftLinear D S C χ z m p ρ| ≤
          (18 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
            |deriv (χ m) p.1| * T.H (T.sample m) ^ (3 / 4 : ℝ) ∧
        |returnCorrectionSpeedLinear D S C χ z m p ρ| ≤
          (18 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading 1 ρ) *
            |deriv (χ m) p.1| * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  let hdata := hN.exists_uniform_inverse_angular_jets hS hT
  let base' : ℕ := hdata.choose
  let ε' : ℝ := hdata.choose_spec.choose
  have hb : base ≤ base' := hdata.choose_spec.choose_spec.1
  have hε' : 0 < ε' := hdata.choose_spec.choose_spec.2.1
  have hεε : ε' ≤ ε := hdata.choose_spec.choose_spec.2.2.1
  have hnew : N01Properties D T S C base' loss ε' := hdata.choose_spec.choose_spec.2.2.2.1
  have hbound := hdata.choose_spec.choose_spec.2.2.2.2
  exact ⟨base', ε', hb, hε', hεε, hnew, fun z hz hsector χ ρ m p hp =>
    hnew.returnCorrectionDriftSpeedLinear_weighted_abs_bound
      hS hT hz hsector (hbound z hz hsector).1 χ ρ m p hp⟩

end ContinuousFlexibility.Statements

