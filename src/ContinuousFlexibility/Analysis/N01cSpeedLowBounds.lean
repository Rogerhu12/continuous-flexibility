import ContinuousFlexibility.Analysis.N01cSpeedBoundsRestriction
import ContinuousFlexibility.Analysis.N01cStateInterpolation
import ContinuousFlexibility.Analysis.N01cMaterialAbsorption
import ContinuousFlexibility.Analysis.OneHighCircleRealSobolev
import ContinuousFlexibility.Analysis.OneHighCircleFourierRealAlgebra

/-!
# Uniform fixed-order speed bounds and circle endpoint norms

Only a prescribed finite spatial order is used to enlarge the common base.
The actual parameter-order-zero tower is evaluated at its genuine value;
the circle estimate uses the actual zeroth and highest angular jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

theorem n01c_smoothDirections_zero_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (center : E)
    {x : E} (hx : x ∈ U) {M : ℝ} (hM : 0 ≤ M)
    (hhigh : p high (x - center) ≤ 1)
    (hbound : |J.D 0 x Fin.elim0| ≤
      M * oneHighVariationWeight p base high (x - center) Fin.elim0) :
    |f x| ≤ 2 * M := by
  have h := hbound
  rw [J.zero x hx] at h
  have hweight : oneHighVariationWeight p base high (x - center) Fin.elim0 =
      1 + p high (x - center) := by
    simp [oneHighVariationWeight]
  rw [hweight] at h
  nlinarith [mul_le_mul_of_nonneg_left hhigh hM]

private theorem n01c_circle_l2_le_pointwise
    {P : ℝ} [Fact (0 < P)] (f : C(AddCircle P, ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ θ : ℝ, |f (θ : AddCircle P)| ≤ M) :
    (eLpNorm f 2 AddCircle.haarAddCircle).toReal ≤ M := by
  have h := circle_l2_le_of_norm_le f (M • (1 : C(AddCircle P, ℝ))) (by
    intro θ
    refine QuotientAddGroup.induction_on θ ?_
    intro t
    simpa only [Real.norm_eq_abs, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one, abs_of_nonneg hM] using hf t)
  rw [circle_l2_const_smul _ hM,
    ← circle_real_sobolevNorm_zero_eq_l2 (1 : C(AddCircle P, ℝ)),
    circle_real_sobolevNorm_one, mul_one] at h
  exact h

theorem circle_sobolevNorm_le_pointwiseJetBounds
    {P : ℝ} [Fact (0 < P)] (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ n : ℕ, ∀ θ : ℝ,
      HasDerivAt (fun η : ℝ => f n (η : AddCircle P))
        (f (n + 1) (θ : AddCircle P)) θ)
    (s : ℕ) {M₀ Mₛ : ℝ} (hM₀ : 0 ≤ M₀) (hMₛ : 0 ≤ Mₛ)
    (hzero : ∀ θ : ℝ, |f 0 (θ : AddCircle P)| ≤ M₀)
    (htop : ∀ θ : ℝ, |f s (θ : AddCircle P)| ≤ Mₛ) :
    circleRealSobolevNorm (s : ℝ) (f 0) ≤ (2 : ℝ) ^ s * (M₀ + Mₛ) :=
  (circle_real_sobolevNorm_le_derivative_endpoints f hderiv s).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (n01c_circle_l2_le_pointwise (f 0) hM₀ hzero)
        (n01c_circle_l2_le_pointwise (f s) hMₛ htop)) (by positivity))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- A fixed angular order is uniformly bounded after one fixed enlargement
of the base. No high-order smallness is used for the later flow bounds. -/
theorem n01_speedDifference_fixedOrder_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) (s : ℕ) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ M : ℝ, 0 < M ∧
      ∀ z ∈ stateNeighborhood S C base' (min ε (1 / 2)), ∀ m b p,
        b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
          |characteristicSpeedFamily D S C 0 b p z| ≤ M := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  obtain ⟨d, hd⟩ := hSpeed.2 0
  obtain ⟨B, hB, hbound⟩ := hd s
  obtain ⟨RH, hRH, hweight⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) B
  let base' : ℕ := max base (s + loss + d)
  refine ⟨base', le_max_left _ _, (2 * B) * RH,
    mul_pos (mul_pos (by norm_num) hB) hRH, ?_⟩
  intro z hz m b p hb hp
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_subset (le_max_left _ _) (min_le_left _ _) hz
  have hhigh : pairGrading (stateGrading S) realGrading (s + loss + d)
      (z - (C.referenceState, 0)) ≤ 1 :=
    (((jointStateGrading_monotone S (le_max_right base (s + loss + d)))
      (z - (C.referenceState, 0))).trans
        (jointStateGrading_displacement_lt_one (min_le_right ε (1 / 2)) hz).le)
  obtain ⟨J, hJ⟩ := hbound m 0 b p (by simpa only [zero_add] using hb) hp
  have hsample := materialSample_mem_radialCore hT hRef.choose_spec.2.1 (C.cell m)
  have hpos := hT.2.1 _ hsample
  have hM : 0 ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg hpos.2.1.le _))
      (Real.rpow_nonneg hpos.2.2.1.le _)
  have hzero := n01c_smoothDirections_zero_bound J
    (pairGrading (stateGrading S) realGrading) base (s + loss + d)
    (C.referenceState, 0) hzold hM hhigh
    (by simpa only [pow_zero, one_mul] using hJ z hzold Fin.elim0)
  calc
    _ ≤ 2 * (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B) := hzero
    _ = (2 * B) * (T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B) := by ring
    _ ≤ (2 * B) * RH :=
      mul_le_mul_of_nonneg_left (hweight _ hsample) (by positivity)

end ContinuousFlexibility.Blueprint
