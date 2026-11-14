module

public import ContinuousFlexibility.Analysis.N08OpticalControlType

/-!
# The half-weight bound for the genuine optical control response

The raw control derivative bound is combined with the relative radicand
bound, rather than with an unproved lower bound on the reference slope.
Their product loses only half the circle weight after taking a square root.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

theorem n08_sqrtAffine_response_sq_bound {A B R W L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hW : 0 < W)
    (hrelative : R * W * |B| ≤ A) (hraw : |B| ≤ L) :
    (B / Real.sqrt A) ^ 2 ≤ L / (R * W) := by
  have hprod : B ^ 2 * (R * W) ≤ L * A := by
    calc
      B ^ 2 * (R * W) = |B| * (R * W * |B|) := by
        rw [← sq_abs B]
        ring
      _ ≤ |B| * A := mul_le_mul_of_nonneg_left hrelative (abs_nonneg B)
      _ ≤ L * A := mul_le_mul_of_nonneg_right hraw hA.le
  rw [div_pow, Real.sq_sqrt hA.le]
  exact (div_le_div_iff₀ hA (mul_pos hR hW)).mpr hprod

private theorem n08_sqrtAffine_weighted_response_sq_bound
    {A d r ε p H β : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hp : 0 ≤ p) (hH : 0 < H)
    (hrelative : (ε / (1 + p)) * |H ^ β * (-d / r)| ≤ A) :
    (d / r / Real.sqrt A) ^ 2 ≤
      |d / r| * ((1 + p) / ε) * H ^ (-β) := by
  have hp' : 0 < 1 + p := by linarith
  have hW : 0 < H ^ β := Real.rpow_pos_of_pos hH β
  have hrad : 0 < ε / (1 + p) := div_pos hε hp'
  have hrelative' : (ε / (1 + p)) * H ^ β * |-d / r| ≤ A := by
    simpa only [abs_mul, abs_of_pos hW, mul_assoc] using hrelative
  have hbound := n08_sqrtAffine_response_sq_bound hA hrad hW hrelative' le_rfl
  have heq : |-d / r| / ((ε / (1 + p)) * H ^ β) =
      |d / r| * ((1 + p) / ε) * H ^ (-β) := by
    rw [neg_div, abs_neg, Real.rpow_neg hH.le]
    field_simp [hε.ne', hp'.ne', hW.ne']
    <;> ring
  rw [heq] at hbound
  simpa only [neg_div, neg_sq] using hbound

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem n08_control_reference_radicand_pos
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
    0 < -deriv D.w r / (r * D.w r) := by
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hC := hN.2.2.2.1
  have hcore : r ∈ radialCore D :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  exact div_pos (neg_pos.mpr (hC.2.2.2.1 m r hr))
    (mul_pos (hg.1.trans hcore.1) (hg.2.2.2.2.1 r hcore))

theorem n08_control_optical_response_sq_bound
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
    (deriv (C.control m) r / r / opticalSpeed D.w r) ^ 2 ≤
      |deriv (C.control m) r / r| *
        ((1 + stateGrading S base (0, 0, n08ControlBasis hS m, 0)) / ε) *
        T.H (T.sample m) ^ (-(3 / 4 : ℝ)) :=
  n08_sqrtAffine_weighted_response_sq_bound
    (A := -deriv D.w r / (r * D.w r)) (d := deriv (C.control m) r) (r := r)
    (ε := ε) (p := stateGrading S base (0, 0, n08ControlBasis hS m, 0))
    (H := T.H (T.sample m)) (β := (3 / 4 : ℝ))
    (n08_control_reference_radicand_pos hN m r hr) hN.2.1
    (apply_nonneg (stateGrading S base) (0, 0, n08ControlBasis hS m, 0))
    (n08_materialSample_H_pos hT hN.1.1 m)
    (n08_controlBasis_radical_relative_bound hS hT hN m r hr)

/-- The only label losses are powers of the actual material weights.
The square of the response loses one `H^β`, hence the response itself
loses half that weight. -/
theorem n08_control_optical_response_sq_envelope
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      (deriv (C.control m) r / r / opticalSpeed D.w r) ^ 2 ≤
        K * T.E0 (T.sample (C.cell m)) ^ B * T.M (T.sample m) ^ base *
          T.H (T.sample m) ^ (-(3 / 4 : ℝ)) := by
  have hdata := hN
  obtain ⟨_, _, _, _, _, hjets, _⟩ := hdata
  obtain ⟨B, hB, hjet⟩ := hjets 1
  let c := n08ControlBasisConstant base
  have hc : 0 ≤ c := n08ControlBasisConstant_nonneg base
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  let K := B * (1 + c) / (D.a * ε)
  have hK : 0 < K := div_pos (mul_pos hB (by linarith)) (mul_pos hg.1 hN.2.1)
  refine ⟨K, B, hK, hB, ?_⟩
  intro m r hr
  have hm := n08_material_sample_bounds hN.1.1 hT m
  have hcore : r ∈ radialCore D :=
    ⟨(hN.2.2.2.1.1 m).1.trans hr.1, hr.2.trans (hN.2.2.2.1.1 m).2.2⟩
  have hrpos : 0 < r := hg.1.trans hcore.1
  have hraw : |deriv (C.control m) r / r| ≤
      B * T.E0 (T.sample (C.cell m)) ^ B / D.a := by
    rw [abs_div, abs_of_pos hrpos]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) hg.1 hcore.1.le).trans
      (div_le_div_of_nonneg_right (by simpa only [iteratedDeriv_one] using hjet m r hr)
        hg.1.le)
  have hp : 1 + stateGrading S base (0, 0, n08ControlBasis hS m, 0) ≤
      (1 + c) * T.M (T.sample m) ^ base := by
    rw [n08_controlDirection_grading]
    have hh := n08ControlBasis_grading_le hS m base hm.1 hm.2
    have hone : 1 ≤ T.M (T.sample m) ^ base := one_le_pow₀ hm.2
    dsimp only [c]
    nlinarith only [hh, hone]
  have hp' := div_le_div_of_nonneg_right hp hN.2.1.le
  have hpnonneg : 0 ≤ 1 + stateGrading S base (0, 0, n08ControlBasis hS m, 0) :=
    add_nonneg zero_le_one (apply_nonneg _ _)
  have hH : 0 ≤ T.H (T.sample m) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hm.1.le _
  have hb := (n08_control_optical_response_sq_bound hS hT hN m r hr).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hraw hp' (div_nonneg hpnonneg hN.2.1.le)
        ((abs_nonneg _).trans hraw)) hH)
  convert hb using 1 <;> dsimp only [K] <;>
    field_simp [hg.1.ne', hN.2.1.ne'] <;> ring

end ContinuousFlexibility.Statements
