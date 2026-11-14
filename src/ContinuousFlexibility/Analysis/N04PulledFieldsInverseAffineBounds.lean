module

public import ContinuousFlexibility.Analysis.N04RealizationHeightGraphComposition
public import ContinuousFlexibility.Analysis.N01cFiniteParameterProducts
public import ContinuousFlexibility.Analysis.N04RealizationMixedSlotBudget

/-!
# Affine reconstruction of the actual inverse point

Positive jets of the constant radial origin vanish. The unwrapped angle
contributes only its linear angular projection, which vanishes on a
positive-state pure word. Thus reconstructing the actual point preserves
the positive-parameter height factor of its two normalized atoms.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

def n04PulledFields_inverseAngleProjection : (X × PolarPoint) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ X PolarPoint)

/-- The formula is for any genuine tower of the same reconstructed
point, independently of the way that tower was built. -/
theorem n04PulledFields_inverseAffine_D_apply
    {W : Set (X × PolarPoint)} {r θ : X × PolarPoint → ℝ}
    {φ : X × PolarPoint → PolarPoint}
    (JR : SmoothDirections W r) (JT : SmoothDirections W θ)
    (Jφ : SmoothDirections W φ) (origin length : ℝ)
    (heq : ∀ z ∈ W, φ z = (origin + length * r z, z.2.2 + θ z))
    {n : ℕ} (hn : 0 < n) {z : X × PolarPoint} (hz : z ∈ W)
    (v : Fin n → X × PolarPoint) :
    Jφ.D n z v =
      (length * JR.D n z v,
        continuousLinearJets (n04PulledFields_inverseAngleProjection (X := X)) n z v +
          JT.D n z v) := by
  let JC := smoothDirections_constant JR.open_domain origin
  let L : ℝ →L[ℝ] ℝ := length • ContinuousLinearMap.id ℝ ℝ
  let JM := smoothDirections_postcompCLM JR L
  let JA := (smoothDirectionsLinear (n04PulledFields_inverseAngleProjection (X := X))).restrict
    JR.open_domain (subset_univ W)
  let JP := smoothDirectionsUniformProd (smoothDirectionsAdd JC JM) (smoothDirectionsAdd JA JT)
  let JQ : SmoothDirections W φ := JP.congrOn (fun y hy => by
    simpa only [Function.comp_apply, L, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, n04PulledFields_inverseAngleProjection, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd'] using (heq y hy).symm)
  have hmul : JM.D n z v = length * JR.D n z v := by
    exact (smoothDirections_postcompCLM_D_apply JR L n z v).trans
      (by simp only [L, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul])
  have hangle : JA.D n z v =
      continuousLinearJets (n04PulledFields_inverseAngleProjection (X := X)) n z v := rfl
  rw [Jφ.unique JQ n z hz]
  change (JC.D n z v + JM.D n z v, JA.D n z v + JT.D n z v) = _
  rw [smoothDirections_D_constant JC hn hz v, zero_add, hmul, hangle]

private theorem n04PulledFieldsInverseAffine_angle_zero
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (hw : w.stateArity ≠ 0)
    (z : X × PolarPoint) (v : Fin n → X × PolarPoint)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    continuousLinearJets (n04PulledFields_inverseAngleProjection (X := X)) n z v = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          have hsum := w.stateArity_eq_sum
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
          cases hflag : w.isState 0 with
          | false =>
              have hzero : w.stateArity = 0 := by
                simpa only [hflag, Bool.false_eq_true, if_false] using hsum
              exact False.elim (hw hzero)
          | true =>
              have hzero := congrArg Prod.snd (hspatial 0 hflag)
              simpa only [continuousLinearJets, ContinuousMultilinearMap.ofSubsingleton_apply_apply,
                n04PulledFields_inverseAngleProjection, ContinuousLinearMap.comp_apply,
                ContinuousLinearMap.coe_snd', Prod.snd_zero] using hzero
      | succ n => simp only [continuousLinearJets, zero_apply]

private theorem n04PulledFieldsInverseAffine_angle_weight
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (offset : ℕ)
    (z : X × PolarPoint) (v : Fin n → X × PolarPoint)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0)
    {H t : ℝ} (hH : 0 ≤ H) (ht : 1 ≤ t) :
    |continuousLinearJets (n04PulledFields_inverseAngleProjection (X := X)) n z v| ≤
      parameterHeightWeight H w.stateArity *
        t ^ (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset) := by
  by_cases hw : w.stateArity = 0
  · simp only [parameterHeightWeight, hw, ite_true, one_mul]
    have hcoord (i : Fin n) :
        (normSeminorm ℝ ℝ) (n04PulledFields_inverseAngleProjection (v i)) ≤ 1 := by
      have hh : |(v i).2.2| ≤ ‖(v i).2‖ := by
        simpa only [Real.norm_eq_abs] using norm_snd_le (v i).2
      simpa only [coe_normSeminorm, Real.norm_eq_abs, n04PulledFields_inverseAngleProjection,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'] using
        hh.trans (hphysical i)
    have hjet := n04Realization_linearJet_seminorm_le
      (n04PulledFields_inverseAngleProjection (X := X)) (normSeminorm ℝ ℝ)
      hn z v zero_le_one hcoord
    have hbound : |continuousLinearJets
        (n04PulledFields_inverseAngleProjection (X := X)) n z v| ≤ 1 := by
      simpa only [coe_normSeminorm, Real.norm_eq_abs] using hjet
    exact hbound.trans (one_le_pow₀ ht)
  · rw [n04PulledFieldsInverseAffine_angle_zero hn w hw z v hspatial, abs_zero]
    exact mul_nonneg (parameterHeightWeight_nonneg hH _) (pow_nonneg (zero_le_one.trans ht) _)

/-- The two actual scalar atom bounds reconstruct a vector bound without
adding an unweighted term at positive parameter order. -/
theorem n04PulledFields_inverseAffine_pureWord_bound
    {W : Set (X × PolarPoint)} {r θ : X × PolarPoint → ℝ}
    {φ : X × PolarPoint → PolarPoint}
    (JR : SmoothDirections W r) (JT : SmoothDirections W θ)
    (Jφ : SmoothDirections W φ) (origin length : ℝ)
    (heq : ∀ z ∈ W, φ z = (origin + length * r z, z.2.2 + θ z))
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (offset : ℕ)
    {z : X × PolarPoint} (hz : z ∈ W) (v : Fin n → X × PolarPoint)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0)
    {A H t : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hr : |JR.D n z v| ≤ A * parameterHeightWeight H w.stateArity *
      t ^ (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset))
    (hθ : |JT.D n z v| ≤ A * parameterHeightWeight H w.stateArity *
      t ^ (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset)) :
    ‖Jφ.D n z v‖ ≤ (|length| * A + A + 1) * parameterHeightWeight H w.stateArity *
      t ^ (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset) := by
  let Q : ℝ := parameterHeightWeight H w.stateArity *
    t ^ (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset)
  have hQ : 0 ≤ Q :=
    mul_nonneg (parameterHeightWeight_nonneg hH _) (pow_nonneg (zero_le_one.trans ht) _)
  have hr' : |JR.D n z v| ≤ A * Q := by simpa only [Q, mul_assoc] using hr
  have hθ' : |JT.D n z v| ≤ A * Q := by simpa only [Q, mul_assoc] using hθ
  have hlinear : |continuousLinearJets
      (n04PulledFields_inverseAngleProjection (X := X)) n z v| ≤ Q :=
    n04PulledFieldsInverseAffine_angle_weight hn w offset z v hphysical hspatial hH ht
  have hrad : |length * JR.D n z v| ≤ (|length| * A + A + 1) * Q := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left hr' (abs_nonneg length)
    nlinarith [mul_nonneg hA hQ]
  have hang : |continuousLinearJets
      (n04PulledFields_inverseAngleProjection (X := X)) n z v + JT.D n z v| ≤
        (|length| * A + A + 1) * Q := by
    have hh := (abs_add_le
      (continuousLinearJets (n04PulledFields_inverseAngleProjection (X := X)) n z v)
      (JT.D n z v)).trans (add_le_add hlinear hθ')
    have hnonneg := mul_nonneg (mul_nonneg (abs_nonneg length) hA) hQ
    nlinarith
  rw [n04PulledFields_inverseAffine_D_apply JR JT Jφ origin length heq hn hz v,
    Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  simpa only [Q, mul_assoc] using max_le hrad hang

end ContinuousFlexibility.Analysis
