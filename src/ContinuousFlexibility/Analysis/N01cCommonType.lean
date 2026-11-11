import ContinuousFlexibility.Analysis.N01cRelativeControl
import ContinuousFlexibility.Analysis.N01cShiftedSampleWeights
import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# A common type neighbourhood from quantitative reference nondegeneracy

The lower bound below is a primitive statement about the reference profile.
It is an explicit input, not a conclusion extracted from the current N01b
interface. The actual control second-jet estimate, its endpoint factor,
the actual circle-mean estimate, and material absorption then give one
radius for all components and every low state order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Cancellation of the coefficient powers in a relative control estimate. -/
theorem small_logControl_amplitude
    {a r E A K κ : ℝ} (har : a ≤ r) (hE : 0 < E)
    (hA : 0 < A) (hK : 0 < K)
    (hsmall : |κ| * E ^ (A + K) ≤ a / (2 * A * K)) :
    |κ| * (A * E ^ A) ≤ r * (K⁻¹ * E ^ (-K)) / 2 := by
  have hpow : E ^ (A + K) * E ^ (-K) = E ^ A := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  calc
    |κ| * (A * E ^ A) = A * (|κ| * E ^ (A + K)) * E ^ (-K) := by
      rw [mul_assoc A, mul_assoc |κ|, hpow]
      ring
    _ ≤ A * (a / (2 * A * K)) * E ^ (-K) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hA.le)
        (Real.rpow_pos_of_pos hE (-K)).le
    _ = a * (K⁻¹ * E ^ (-K)) / 2 := by
      field_simp [hA.ne', hK.ne']
      <;> ring
    _ ≤ r * (K⁻¹ * E ^ (-K)) / 2 := by
      have hc : 0 ≤ K⁻¹ * E ^ (-K) :=
        mul_nonneg (inv_nonneg.mpr hK.le) (Real.rpow_pos_of_pos hE (-K)).le
      nlinarith only [mul_le_mul_of_nonneg_right har hc]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- One radius bounds the true relative optical perturbation on every
component, and hence the actual perturbed optical square on both sides. -/
theorem n01_exists_common_opticalBounds_of_referenceLower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hlower : ∃ K : ℝ, 0 < K ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
          min (r - C.left m) (C.right m - r) ≤
        -deriv D.w r / (r * D.w r)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ base : ℕ, ∀ z ∈ stateNeighborhood S C base ε,
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
        |stateKappa S z.1 m * deriv (C.control m) r / r| ≤
          (-deriv D.w r / (r * D.w r)) / 2 ∧
        (-deriv D.w r / (r * D.w r)) / 2 ≤
          -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r) ∧
        -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r) ≤
          3 * (-deriv D.w r / (r * D.w r)) / 2 := by
  obtain ⟨K, hK, hQ⟩ := hlower
  obtain ⟨A, hApos, hcontrol⟩ := n01_controlFirstJet_le_endpointDistance hT hA
  obtain ⟨B, hB, hindex⟩ := hA.2.2.2.1
  obtain ⟨M, hM, hweight⟩ := n01c_materialSample_shifted_weight_bounded hT hA.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) (A + K) hB.le
  let c : ℝ := (1 / Real.pi) * Real.sqrt Real.pi
  have hc : 0 < c :=
    mul_pos (div_pos zero_lt_one Real.pi_pos) (Real.sqrt_pos.mpr Real.pi_pos)
  obtain ⟨_, hprofile⟩ := hA.1.1
  have ha : 0 < D.a := hprofile.1.1
  let ε : ℝ := D.a / (2 * A * K * c * M)
  have hε : 0 < ε := div_pos ha (by positivity)
  refine ⟨ε, hε, fun base z hz m r hr => ?_⟩
  have hC := hA.2.2.1
  have hcore : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hrad : 0 < r := ha.trans hcore.1
  have hsample : T.sample (C.cell m) ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hprofile.2.1 (C.cell m)
  have hE : 0 < T.E0 (T.sample (C.cell m)) := (hT.2.1 _ hsample).2.2.1
  have hκ := abs_stateKappa_le_radius hS hT hA.1.1 hA.2.1 hz m
  have hshift : |(D.cellIndex m : ℝ) - D.cellIndex (C.cell m)| ≤ B :=
    (abs_sub_comm _ _).trans_le (hindex m)
  have hsmall : |stateKappa S z.1 m| *
      T.E0 (T.sample (C.cell m)) ^ (A + K) ≤ D.a / (2 * A * K) := by
    calc
      _ ≤ ((c * ε) * T.H (T.sample m) ^ (3 / 4 : ℝ)) *
          T.E0 (T.sample (C.cell m)) ^ (A + K) :=
        mul_le_mul_of_nonneg_right hκ (Real.rpow_pos_of_pos hE (A + K)).le
      _ = (c * ε) * (T.H (T.sample m) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ (A + K)) := mul_assoc _ _ _
      _ ≤ (c * ε) * M :=
        mul_le_mul_of_nonneg_left (hweight m (C.cell m) hshift) (mul_pos hc hε).le
      _ = D.a / (2 * A * K) := by
        dsimp only [ε]
        field_simp [hApos.ne', hK.ne', hc.ne', hM.ne']
        <;> ring
  have hδ : 0 ≤ min (r - C.left m) (C.right m - r) :=
    le_min (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2.le)
  have hrelative := optical_relative_control_bound hδ hrad (hQ m r hr)
    (hcontrol m r hr)
    (small_logControl_amplitude hcore.1.le hE hApos hK hsmall)
  refine ⟨hrelative, ?_⟩
  rw [n01_stateProfile_opticalSquare_eq hA z.1 m hr]
  exact opticalSquare_sub_bounds hrelative

/-- The same common radius preserves the derivative sign of the actual
profile on every original negative component. -/
theorem n01_exists_common_negativeType_of_referenceLower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hlower : ∃ K : ℝ, 0 < K ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
          min (r - C.left m) (C.right m - r) ≤
        -deriv D.w r / (r * D.w r)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ base : ℕ, ∀ z ∈ stateNeighborhood S C base ε,
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
        deriv (stateProfile D S C z.1) r < 0 := by
  obtain ⟨ε, hε, hbounds⟩ :=
    n01_exists_common_opticalBounds_of_referenceLower hS hT hA hlower
  obtain ⟨_, hprofile⟩ := hA.1.1
  have hC := hA.2.2.1
  refine ⟨ε, hε, fun base z hz m r hr => ?_⟩
  have hcore : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hrad : 0 < r := hprofile.1.1.trans hcore.1
  have hw : 0 < D.w r := hprofile.1.2.2.2.2.1 r hcore
  have hQ : 0 < -deriv D.w r / (r * D.w r) :=
    div_pos (neg_pos.mpr (hC.2.2.2.1 m r hr)) (mul_pos hrad hw)
  have hwz : 0 < stateProfile D S C z.1 r := by
    exact mul_pos hw (Real.exp_pos _)
  have hQz : 0 < -deriv (stateProfile D S C z.1) r /
      (r * stateProfile D S C z.1 r) :=
    (half_pos hQ).trans_le (hbounds base z hz m r hr).2.1
  exact neg_pos.mp ((div_pos_iff_of_pos_right (mul_pos hrad hwz)).mp hQz)

end ContinuousFlexibility.Statements
