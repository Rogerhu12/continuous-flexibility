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

private theorem n08_injected_control_grading_pair_le
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (base high : ℕ) (u : F)
    {A B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 1 ≤ M)
    (hb : q base u ≤ A * M ^ base) (hh : q high u ≤ B * M ^ high) :
    pairGrading p (pairGrading realGrading (pairGrading q q)) base (0, 0, u, 0) +
      pairGrading p (pairGrading realGrading (pairGrading q q)) high (0, 0, u, 0) ≤
        (A + B) * M ^ (base + high) := by
  rw [n08_injected_control_grading, n08_injected_control_grading]
  have h₁ := hb.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.le_add_right base high)) hA)
  have h₂ := hh.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.le_add_left high base)) hB)
  simpa only [add_mul] using add_le_add h₁ h₂

theorem n08_controlDirection_grading (S : PhysicalSpacesData) (s : ℕ) (u : CircleSpace S) :
    stateGrading S s (0, 0, u, 0) = (S.circle (3 / 4 : ℝ)).grading s u :=
  n08_injected_control_grading (heightPairGrading S) (S.circle (3 / 4 : ℝ)).grading s u

theorem n08_material_sample_bounds {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (m : ℕ) :
    0 < T.H (T.sample m) ∧ 1 ≤ T.M (T.sample m) := by
  obtain ⟨B, hB⟩ := hD
  have hp := hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hB.2.1 m)
  exact ⟨hp.2.1, hp.2.2.2⟩

private theorem n08_material_sample_E0_nonneg {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (m : ℕ) :
    0 ≤ T.E0 (T.sample m) := by
  obtain ⟨B, hB⟩ := hD
  exact (hT.2.1 _ (materialSample_mem_radialCore hT hB.2.1 m)).2.2.1.le

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
        T.M (T.sample i) ^ (base + high) :=
  n08_injected_control_grading_pair_le (heightPairGrading S)
    (S.circle (3 / 4 : ℝ)).grading base high (n08ControlBasis hS i)
    (n08ControlBasisConstant_nonneg base) (n08ControlBasisConstant_nonneg high) hM
    (n08ControlBasis_grading_le hS i base hH hM)
    (n08ControlBasis_grading_le hS i high hH hM)

private theorem n08_profile_modes_bound {E I J : Type*}
    (L : E → ℝ → ℝ) (v : I → E) (g : I → ℝ → ℝ) (p : E → ℝ)
    (w : ℝ → ℝ) (region : J → Set ℝ) (H E0 : J → ℝ) (R : I → ℝ) (s : ℕ)
    {A : ℝ} (hA : 0 ≤ A) (hH : ∀ m, 0 ≤ H m) (hE : ∀ m, 0 ≤ E0 m)
    (hg : ∀ i, p (v i) ≤ A * R i) (heq : ∀ i, L (v i) = g i)
    (hb : ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ region m → ∀ u : E,
      |iteratedDeriv s (fun t => w t * L u t) r| ≤
        B * H m * E0 m ^ B * p u) :
    ∃ B K : ℝ, 0 < B ∧ 0 ≤ K ∧ ∀ i m r, r ∈ region m →
      |iteratedDeriv s (fun t => w t * g i t) r| ≤
        K * H m * E0 m ^ B * R i := by
  obtain ⟨B, hB, hb⟩ := hb
  refine ⟨B, B * A, hB, mul_nonneg hB.le hA, ?_⟩
  intro i m r hr
  have h := hb m r hr (v i)
  rw [heq i] at h
  calc
    _ ≤ B * H m * E0 m ^ B * p (v i) := h
    _ ≤ B * H m * E0 m ^ B * (A * R i) :=
      mul_le_mul_of_nonneg_left (hg i)
        (mul_nonneg (mul_nonneg hB.le (hH m)) (Real.rpow_nonneg (hE m) B))
    _ = B * A * H m * E0 m ^ B * R i := by ring

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
          T.M (T.sample i) ^ (base + (s + loss)) :=
  n08_profile_modes_bound (n08_stateLogProfile D S C)
    (fun i => (0, 0, n08ControlBasis hS i, 0)) (n08WeightedControlProfile T C)
    (fun v => stateGrading S base v + stateGrading S (s + loss) v)
    D.w D.cells (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => T.E0 (T.sample m)) (fun i => T.M (T.sample i) ^ (base + (s + loss))) s
    (add_nonneg (n08ControlBasisConstant_nonneg base)
      (n08ControlBasisConstant_nonneg (s + loss)))
    (fun m => Real.rpow_nonneg (n08_material_sample_bounds hN.1.1 hT m).1.le _)
    (n08_material_sample_E0_nonneg hN.1.1 hT)
    (fun i => n08_controlBasis_grading_pair_le hS i base (s + loss)
      (n08_material_sample_bounds hN.1.1 hT i).1 (n08_material_sample_bounds hN.1.1 hT i).2)
    (n08_logProfile_controlBasis hS) (n08_logProfile_reference_jet_bound hT hS hN s)

end ContinuousFlexibility.Statements
