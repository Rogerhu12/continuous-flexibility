import ContinuousFlexibility.Analysis.N08ControlBasis
import ContinuousFlexibility.Analysis.N08ProfileJetBounds

/-!
# The genuine weighted single-control profile modes

The physical constant circle basis realizes a weighted unit control exactly.
Applying the N01 profile-jet estimate to this same basis gives estimates at
the actual reference cell containing the evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n08_injected_control_grading
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (s : ℕ) (u : F) :
    pairGrading p (pairGrading realGrading (pairGrading q q)) s (0, 0, u, 0) = q s u := by
  change p s 0 + (realGrading s 0 + (q s u + q s 0)) = q s u
  rw [map_zero, map_zero, map_zero, zero_add, zero_add, add_zero]

theorem n08_controlDirection_grading (S : PhysicalSpacesData) (s : ℕ) (u : CircleSpace S) :
    stateGrading S s (0, 0, u, 0) = (S.circle (3 / 4 : ℝ)).grading s u :=
  n08_injected_control_grading (heightPairGrading S) (S.circle (3 / 4 : ℝ)).grading s u

theorem n08_material_sample_bounds {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (m : ℕ) :
    0 < T.H (T.sample m) ∧ 1 ≤ T.M (T.sample m) := by
  obtain ⟨B, hB⟩ := hD
  have hp := hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hB.2.1 m)
  exact ⟨hp.2.1, hp.2.2.2⟩

def n08WeightedControlProfile (T : MaterialData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (m : ℕ) (r : ℝ) : ℝ :=
  T.H (T.sample m) ^ (3 / 4 : ℝ) * C.control m r

theorem n08_logProfile_controlBasis
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    n08_stateLogProfile D S C (0, 0, n08ControlBasis hS m, 0) =
      n08WeightedControlProfile T C m := by
  funext r
  rw [n08_stateLogProfile_kappaDirection]
  simp_rw [n08ControlBasis_mean]
  rw [tsum_eq_single m (fun n hnm => by rw [if_neg hnm, zero_mul]), if_pos rfl]
  rfl

private theorem n08_controlBasis_grading_pair_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (i base high : ℕ)
    (hH : 0 < T.H (T.sample i)) (hM : 1 ≤ T.M (T.sample i)) :
    stateGrading S base (0, 0, n08ControlBasis hS i, 0) +
      stateGrading S high (0, 0, n08ControlBasis hS i, 0) ≤
      (n08ControlBasisConstant base + n08ControlBasisConstant high) *
        T.M (T.sample i) ^ (base + high) := by
  rw [n08_controlDirection_grading, n08_controlDirection_grading]
  have h₁ := (n08ControlBasis_grading_le hS i base hH hM).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.le_add_right base high))
      (n08ControlBasisConstant_nonneg base))
  have h₂ := (n08ControlBasis_grading_le hS i high hH hM).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.le_add_left high base))
      (n08ControlBasisConstant_nonneg high))
  simpa only [add_mul] using add_le_add h₁ h₂

/-- The state direction is a genuine physical basis element. The resulting
spatial estimate has independently quantified control label `i` and actual
reference cell `m`; no relation between their locations is required. -/
theorem n08_controlProfile_reference_jet_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B K : ℝ, 0 < B ∧ 0 ≤ K ∧ ∀ i m r, r ∈ D.cells m →
      |iteratedDeriv s (fun t => D.w t * n08WeightedControlProfile T C i t) r| ≤
        K * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          T.M (T.sample i) ^ (base + (s + loss)) := by
  obtain ⟨B, hB, hBj⟩ := n08_logProfile_reference_jet_bound hT hS hN s
  let A := n08ControlBasisConstant base + n08ControlBasisConstant (s + loss)
  have hA : 0 ≤ A := add_nonneg (n08ControlBasisConstant_nonneg _)
    (n08ControlBasisConstant_nonneg _)
  refine ⟨B, B * A, hB, mul_nonneg hB.le hA, ?_⟩
  intro i m r hr
  have hi := n08_material_sample_bounds hN.1.1 hT i
  have hm := n08_material_sample_bounds hN.1.1 hT m
  have hEm : 0 ≤ T.E0 (T.sample m) := by
    obtain ⟨C0, hC0⟩ := hN.1.1
    exact (hT.2.1 _ (materialSample_mem_radialCore hT hC0.2.1 m)).2.2.1.le
  have h := hBj m r hr (0, 0, n08ControlBasis hS i, 0)
  rw [n08_logProfile_controlBasis hS] at h
  have hh := h.trans (mul_le_mul_of_nonneg_left
    (n08_controlBasis_grading_pair_le hS i base (s + loss) hi.1 hi.2)
      (mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg hm.1.le _))
        (Real.rpow_nonneg hEm _)))
  convert hh using 1 <;> dsimp only [A] <;> ring

end ContinuousFlexibility.Statements
