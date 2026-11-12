import ContinuousFlexibility.Analysis.N01CoefficientJointTower
import ContinuousFlexibility.Analysis.N01CoefficientSpatialJets
import ContinuousFlexibility.Analysis.MixedJointTameBounds
import ContinuousFlexibility.Analysis.MaterialSampleShift
import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope
import ContinuousFlexibility.Analysis.ActualRadialCellComparison
import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# The actual coefficient increment retains its sample height gain

The existing joint tower is estimated directly from the original mixed
N01 estimates. The height factor multiplies the whole mixed-to-joint
bound. A fixed scalar postcomposition then removes that factor exactly.
The original base, loss, host and sample are unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

local instance n04IncrementJointStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem n04_increment_sample_E0_power_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K Q : ℝ, 0 < K ∧ 0 ≤ Q ∧ ∀ j,
      T.E0 (T.sample j) ^ R ≤ K * radialE (D.cellIndex j) ^ Q := by
  obtain ⟨d0, L, KH, KE, KM, _, hL, _, hKE, _, hm⟩ :=
    materialSample_global_endpoint_models hT hRef
  obtain ⟨K, Q, hK, hQ, hb⟩ := materialE0_rpow_oneSided_shift hR hL
  have hKE0 : 0 < KE := zero_lt_one.trans_le hKE
  refine ⟨KE ^ R * K * Real.exp Q, Q,
    mul_pos (mul_pos (Real.rpow_pos_of_pos hKE0 _) hK) (Real.exp_pos _), hQ, ?_⟩
  intro j
  rcases hm j with ⟨hx, hdist, _, _, hE, _, _, _⟩
  have hpos := (hT.2.1 _
    (materialSample_mem_radialCore hT hRef.choose_spec.2.1 j)).2.2.1
  have hfirst := Real.rpow_le_rpow hpos.le hE hR
  rw [Real.mul_rpow hKE0.le (materialE0_pos _).le] at hfirst
  have hlast : materialE0 (D.cellIndex j : ℝ) ^ Q =
      Real.exp Q * radialE (D.cellIndex j) ^ Q := by
    rw [radialE_rpow_eq_materialE0, ← mul_assoc, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, one_mul]
  calc
    _ ≤ KE ^ R * materialE0
        (endpointX d0 (Statements.endpointDistance D (T.sample j))) ^ R := hfirst
    _ ≤ KE ^ R * (K * materialE0 (D.cellIndex j : ℝ) ^ Q) :=
      mul_le_mul_of_nonneg_left
        (hb _ _ hx (Nat.cast_nonneg _) (by linarith only [(abs_le.mp hdist).2]))
        (Real.rpow_nonneg hKE0.le _)
    _ = _ := by rw [hlast]; ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

theorem N01Properties.coefficientIncrement_parameterSpatialTower_parameterJet
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (n : ℕ) (x : StateDirections S × ℝ)
    (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ)
    {y : PolarPoint} (hy : y ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    hN.componentCoefficientScalarJet m j hcell i n x v y =
      (hN.coefficientIncrement_parameterSpatialTower hS hT m j hcell i).D
        n (x, y) (fun k => (v k, 0)) := by
  let J := hN.coefficientIncrement_parameterSpatialTower hS hT m j hcell i
  let K := hN.sectorCoefficientTower j i 0 0 y (hcell hy.1)
  exact (hN.componentCoefficientScalarJet_of_mem m j hcell i n x v hy).trans
    (J.pointTower_eq_jointJet (sectorNeighborhood_isOpen S base ε ε)
      y hy K n x hx v)

/-- The same actual joint tower keeps the full sample height gain,
uniformly in both the component and its chosen true host. -/
theorem N01Properties.coefficientIncrement_joint_unit_bound (n : ℕ) :
    ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧
      ∀ (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j) (i : Fin 3),
      ∀ x ∈ sectorNeighborhood S base ε ε,
      ∀ y ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      ∀ v : Fin n → (StateDirections S × ℝ) × PolarPoint,
      (∀ k, pairGrading (sectorGrading S) realGrading base (v k).1 + ‖(v k).2‖ ≤ 1) →
      |(hN.coefficientIncrement_parameterSpatialTower hS hT m j hcell i).D n (x, y) v| ≤
        A * T.H (T.sample j) ^ (3 / 4 : ℝ) * radialE (D.cellIndex j) ^ Q *
          (1 + pairGrading (sectorGrading S) realGrading (n + loss) x +
            ∑ k, pairGrading (sectorGrading S) realGrading (n + loss) (v k).1) := by
  classical
  let data (k : Fin (n + 1)) := hN.componentCoefficientScalarJet_mixed_bound hS hT k n
  let B (k : Fin (n + 1)) : ℝ := (data k).choose
  have hB (k : Fin (n + 1)) : 0 < B k := (data k).choose_spec.1
  choose K P hK hP hKP using fun k : Fin (n + 1) =>
    n04_increment_sample_E0_power_bound hT hN.1.1 (hB k).le
  let A : ℝ := ∑ k : Fin (n + 1), B k * K k
  let Q : ℝ := ∑ k : Fin (n + 1), P k
  have hA : 0 ≤ A := Finset.sum_nonneg (fun k _ => mul_nonneg (hB k).le (hK k).le)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun k _ => hP k)
  refine ⟨(3 : ℝ) ^ n * A, Q, mul_nonneg (pow_nonneg (by norm_num) _) hA, hQ, ?_⟩
  intro m j hcell i x hx y hy v hv
  let p := pairGrading (sectorGrading S) realGrading
  let W := radialE (D.cellIndex j)
  let H := T.H (T.sample j) ^ (3 / 4 : ℝ)
  let J := hN.coefficientIncrement_parameterSpatialTower hS hT m j hcell i
  have hW : 1 ≤ W := one_le_radialE_of_nat _
  have hH : 0 < H := Real.rpow_pos_of_pos
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1 _
  have hinput (k a b : ℕ) (horder : k + a + b ≤ n)
      (u : Fin k → StateDirections S × ℝ) (hu : ∀ t, p base (u t) ≤ 1) :
      |mixedDerivative a b (fun q => J.D k (x, q) (fun t => (u t, 0))) y| ≤
        (A * H * W ^ Q) * ((1 + p (n + loss) x) + ∑ t, p (n + loss) (u t)) := by
    let ik : Fin (n + 1) := ⟨k, by omega⟩
    have hPA : P ik ≤ Q := Finset.single_le_sum (fun t _ => hP t) (Finset.mem_univ ik)
    have hBA : B ik * K ik ≤ A :=
      Finset.single_le_sum (fun t _ => mul_nonneg (hB t).le (hK t).le) (Finset.mem_univ ik)
    have hcoef : B ik * T.E0 (T.sample j) ^ B ik ≤ A * W ^ Q := by
      calc
        _ ≤ (B ik * K ik) * W ^ P ik :=
          (mul_le_mul_of_nonneg_left (hKP ik j) (hB ik).le).trans_eq (by ring)
        _ ≤ (B ik * K ik) * W ^ Q := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hW hPA) (mul_nonneg (hB ik).le (hK ik).le)
        _ ≤ A * W ^ Q := mul_le_mul_of_nonneg_right hBA
          (Real.rpow_nonneg (zero_le_one.trans hW) _)
    have heq : mixedDerivative a b (hN.componentCoefficientScalarJet m j hcell i k x u) y =
        mixedDerivative a b (fun q => J.D k (x, q) (fun t => (u t, 0))) y :=
      mixedDerivative_congr_on_open (isOpen_Ioo.prod isOpen_univ)
        (fun q hq => hN.coefficientIncrement_parameterSpatialTower_parameterJet
          hS hT m j hcell i k x hx u hq) a b hy
    have hraw := (data ik).choose_spec.2 m j hcell i a b (by omega) y hy x hx u
    have hsize : oneHighVariationWeight p base (n + loss) x u ≤
        (1 + p (n + loss) x) + ∑ t, p (n + loss) (u t) :=
      multilinearTameSize_le_affine (p base) (p (n + loss)) k
        (add_nonneg zero_le_one (apply_nonneg _ _)) u hu
    calc
      _ ≤ B ik * H * T.E0 (T.sample j) ^ B ik *
          oneHighVariationWeight p base (n + loss) x u :=
        (congrArg abs heq).symm.trans_le hraw
      _ = H * (B ik * T.E0 (T.sample j) ^ B ik) *
          oneHighVariationWeight p base (n + loss) x u := by ring
      _ ≤ H * (A * W ^ Q) * ((1 + p (n + loss) x) + ∑ t, p (n + loss) (u t)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoef hH.le) hsize
          (multilinearTameSize_nonneg (p base) (p (n + loss)) k
            (add_nonneg zero_le_one (apply_nonneg _ _)) u)
          (mul_nonneg hH.le (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hW) _)))
      _ = _ := by ring
  have hunit (k : Fin n) : p base (v k).1 ≤ 1 ∧ |(v k).2.1| ≤ 1 ∧ |(v k).2.2| ≤ 1 := by
    have hl : p base (v k).1 ≤ 1 :=
      (le_add_of_nonneg_right (norm_nonneg (v k).2)).trans (hv k)
    have hs : ‖(v k).2‖ ≤ 1 :=
      (le_add_of_nonneg_left (apply_nonneg (p base) (v k).1)).trans (hv k)
    refine ⟨hl, ?_, ?_⟩
    · have hfst : |(v k).2.1| ≤ ‖(v k).2‖ := by
        simpa only [Real.norm_eq_abs] using norm_fst_le (v k).2
      exact hfst.trans hs
    · have hsnd : |(v k).2.2| ≤ ‖(v k).2‖ := by
        simpa only [Real.norm_eq_abs] using norm_snd_le (v k).2
      exact hsnd.trans hs
  have hb := J.jointJet_unit_bound_of_mixed_parameter_bounds
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (C.left m) (C.right m)).prod convex_univ))
    (p base) (p (n + loss)) n x hx y hy
    (mul_nonneg (mul_nonneg hA hH.le) (Real.rpow_nonneg (zero_le_one.trans hW) _))
    (add_nonneg zero_le_one (apply_nonneg _ _)) hinput v hunit
  simpa only [mul_assoc] using hb

/-- Normalize by the same fixed sample scalar in every layer of the
existing tower; the original base and loss are retained. -/
theorem N01Properties.coefficientIncrement_normalized_joint_growth
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (i : Fin 3) :
    UniformWeightedJointGrowth (pairGrading (sectorGrading S) realGrading)
      (fun m => radialE (D.cellIndex (j m)))
      (fun m => smoothDirectionsScalarPostcompose
        (hN.coefficientIncrement_parameterSpatialTower hS hT m (j m) (hcell m) i)
        ((T.H (T.sample (j m)) ^ (3 / 4 : ℝ))⁻¹ • ContinuousLinearMap.id ℝ ℝ))
      base loss := by
  intro R hR n
  obtain ⟨A, Q, hA, hQ, hb⟩ := hN.coefficientIncrement_joint_unit_bound hS hT n
  refine ⟨A, Q, hA, hQ, ?_⟩
  intro m x hx _ y hy v hv
  let H := T.H (T.sample (j m)) ^ (3 / 4 : ℝ)
  have hH : 0 < H := Real.rpow_pos_of_pos
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 (j m))).2.1 _
  rw [smoothDirectionsScalarPostcompose_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (inv_pos.mpr hH)]
  have h := mul_le_mul_of_nonneg_left (hb m (j m) (hcell m) i x hx y hy v hv)
    (inv_nonneg.mpr hH.le)
  refine h.trans_eq ?_
  calc
    _ = (H⁻¹ * H) * (A * radialE (D.cellIndex (j m)) ^ Q *
        (1 + pairGrading (sectorGrading S) realGrading (n + loss) x +
          ∑ k, pairGrading (sectorGrading S) realGrading (n + loss) (v k).1)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hH.ne', one_mul]

end ContinuousFlexibility.Statements
