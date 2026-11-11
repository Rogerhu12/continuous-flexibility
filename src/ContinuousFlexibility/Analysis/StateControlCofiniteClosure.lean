import ContinuousFlexibility.Analysis.ControlCellEndpointBounds
import ContinuousFlexibility.Analysis.MaterialSampleCofinite
import ContinuousFlexibility.Analysis.StateControlCofiniteJets

/-!
# Endpoint smoothness without identifying control and reference cells

The nonlinear hypotheses compare the indices used by the control amplitudes
and their derivatives. They do not identify a control interval with a reference
cell. For endpoint smoothness that identification is unnecessary: the weighted
control jets tend uniformly to zero outside a finite set of control indices,
and each of the finitely many exceptional intervals stays away from the ends.

The material comparison is used only at the actual sample of a reference cell,
where its membership hypothesis is available. No rate in the physical radial
coordinate is asserted by this argument.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

/-- Every ordinary control jet, including its actual state amplitude, is
uniformly small on its entire interval outside a finite set of indices. -/
theorem stateKappa_controlJet_eventually_small
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S)
    (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m in cofinite, ∀ r ∈ Ioo (C.left m) (C.right m),
      |stateKappa S x m * iteratedDeriv n (C.control m) r| ≤ η := by
  have hRef : IsAccumulatingProfile D := hN.1.1
  obtain ⟨_, _, _, _, hIndex, hJets, _⟩ := hN
  obtain ⟨B, hB, hindex⟩ := hIndex
  obtain ⟨Kc, hKc, hcontrol⟩ := hJets n
  obtain ⟨Kκ, hKκ, hκ⟩ := stateKappa_weight_bound_of_accumulatingProfile hS hT hRef x
  obtain ⟨δ, K, hδ, hK, henv⟩ :=
    materialSample_endpoint_weight_bound hT hRef (γ := (3 / 4 : ℝ)) (by norm_num) Kc hB.le
  have hcell : Tendsto C.cell cofinite cofinite :=
    controlCell_tendsto_cofinite hRef C.cell hindex
  have hnear : ∀ᶠ m in cofinite, endpointDistance D (T.sample (C.cell m)) < δ :=
    ((materialSample_endpointDistance_tendsto_zero hT hRef).comp hcell).eventually_lt_const hδ
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _, _, hsamp, _, _⟩ := hdata
  obtain ⟨_, _, _, hleft, hright⟩ := hdecay 0 ((3 / 4 : ℝ) / 16) (by norm_num)
  have hweight : Tendsto (fun m => T.H (T.sample m) ^ ((3 / 4 : ℝ) / 16))
      cofinite (𝓝 0) := by
    apply materialSample_tendsto_zero_of_endpoint_limits hT hRef
      (f := fun r => T.H r ^ ((3 / 4 : ℝ) / 16))
    · simpa only [Real.rpow_zero, mul_one] using hleft
    · simpa only [Real.rpow_zero, mul_one] using hright
  have hsmall : ∀ᶠ m in cofinite,
      ((Kκ * Kc) * K) * T.H (T.sample (C.cell m)) ^ ((3 / 4 : ℝ) / 16) < η := by
    have hlim := (hweight.comp hcell).const_mul ((Kκ * Kc) * K)
    rw [mul_zero] at hlim
    exact hlim.eventually_lt_const hη
  obtain ⟨_, hbounds⟩ := hRef
  have hnonneg : 0 ≤ Kκ * Kc := mul_nonneg hKκ hKc.le
  filter_upwards [hnear, hsmall] with m hmnear hmsmall
  intro r hr
  have hi : |(D.cellIndex m : ℝ) - D.cellIndex (C.cell m)| ≤ B :=
    (abs_sub_comm _ _).trans_le (hindex m)
  have hw := henv m (C.cell m) (T.sample (C.cell m))
    (materialSample_mem_radialCore hT hbounds.2.1 (C.cell m))
    (hsamp (C.cell m)) hi hmnear
  have hκ' : 0 ≤ Kκ * T.H (T.sample m) ^ (3 / 4 : ℝ) :=
    (abs_nonneg _).trans (hκ m)
  rw [abs_mul]
  calc
    _ ≤ (Kκ * T.H (T.sample m) ^ (3 / 4 : ℝ)) *
        (Kc * T.E0 (T.sample (C.cell m)) ^ Kc) :=
      mul_le_mul (hκ m) (hcontrol m r hr) (abs_nonneg _) hκ'
    _ = (Kκ * Kc) *
        (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ Kc) := by ring
    _ ≤ (Kκ * Kc) * (K * T.H (T.sample (C.cell m)) ^ ((3 / 4 : ℝ) / 16)) :=
      mul_le_mul_of_nonneg_left hw hnonneg
    _ = ((Kκ * Kc) * K) * T.H (T.sample (C.cell m)) ^ ((3 / 4 : ℝ) / 16) :=
      (mul_assoc _ _ _).symm
    _ ≤ η := hmsmall.le

/-- The original nonlinear hypotheses already give a globally smooth actual
profile. No placement hypothesis for the control intervals is needed. -/
theorem contDiff_stateProfile_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateProfile D S C x) := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨hleft, hright⟩ := stateControlSum_flatJets_of_eventually_small hC x
    (stateKappa_controlJet_eventually_small hS hT hN x)
  obtain ⟨_, hbounds⟩ := hN.1.1
  have hborder : RadialTrueBorder D := hN.1.2.2.2.1
  exact contDiff_stateProfile_of_flat_control_sum hbounds.1 hborder.1 hC x hleft hright

end ContinuousFlexibility.Statements
