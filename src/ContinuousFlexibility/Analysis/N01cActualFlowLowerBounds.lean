import ContinuousFlexibility.Analysis.N01cFlowVariationInput
import ContinuousFlexibility.Analysis.N01cFlowOrderConstants
import ContinuousFlexibility.Analysis.N01cMaterialAbsorption

/-!
# The actual strict lower forcing factors

Only positive parameter orders strictly below the current order occur.
Their already normalized bounds are restricted to the original unit
directions. Global material absorption is permitted for these lower
factors because the forcing head retains its own material weight.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem n01_ordinaryFlowLowerFactors_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss N : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hIH : ∀ k, k < N → 0 < k →
      OrdinaryFlowAngularOrderBound hS hT hA hB hpos loss k) :
    ∃ offset : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ u : OrdinaryFlowVariationInput D S C base ε N,
      ∀ t : ℝ, ∀ ω : FlowForcingChoice N, ∀ i : Fin ω.1.length,
        u.factorNorm hS hT hA hB hpos s t ω i.succ ≤
          A * u.aggregate (s + offset) := by
  let p := pairGrading (stateGrading S) realGrading
  let P := fun (k s high : ℕ) (B : ℝ) =>
    ∀ b : ℕ, b ≤ s → ∀ m,
    ∀ J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m),
    ∀ r : ℝ, ∀ hr : r ∈ Icc (C.left m) (C.right m), ∀ θ : ℝ,
    ∀ x ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
      |(ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J hr b θ).D k x v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight p base high (x - (C.referenceState, 0)) v
  have hprefix := n01c_strict_positive_prefix P N loss
    (fun k s a b A B hab hApos hAB hraw j hj m J r hr θ x hx v =>
      (hraw j hj m J r hr θ x hx v).trans
        (n01c_materialOneHigh_mono p (jointStateGrading_monotone S) base hab
          hApos.le hAB
          (hT.2.1 _ (materialSample_mem_radialCore
            hT hA.1.1.choose_spec.2.1 (C.cell m))).2.1.le
          (hE _ (materialSample_mem_radialCore
            hT hA.1.1.choose_spec.2.1 (C.cell m)))
          (3 / 4 : ℝ) (x - (C.referenceState, 0)) v))
    hIH
  refine n01c_transform_offset_constants _ _ hprefix ?_
  intro offset s B hBpos hbound
  obtain ⟨Q, hQ, hweight⟩ :=
    materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) B
  let M : ℝ := max 1 (B * Q * ((N : ℝ) + 1))
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨(2 : ℝ) ^ (s + 1) * M, mul_pos (by positivity) hM, ?_⟩
  intro u t ω i
  let high := s + offset
  let R : ℝ := u.aggregate high
  have hR : 1 ≤ R := u.aggregate_one_le high
  have hpoint (b : ℕ) (hb : b ≤ s) (θ : ℝ) :
      |ordinaryFlowForcingFactorJet hS hT hA hB hpos u.component u.tower
        u.state u.mem u.plot u.directions t ω i.succ b
          (θ : AddCircle Real.pi)| ≤ M * R := by
    by_cases hi : i ∈ ω.2
    · rw [ordinaryFlowForcingFactorJet_selected hS hT hA hB hpos
        u.component u.tower u.state u.mem u.plot u.directions t ω i hi]
      have hconst : |iteratedDeriv b (fun _ : ℝ => (1 : ℝ)) θ| ≤ 1 := by
        by_cases hb0 : b = 0 <;> simp [iteratedDeriv_const, hb0]
      exact hconst.trans (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hR)
    · by_cases hk : ω.1.partSize i < N
      · rw [ordinaryFlowForcingFactorJet_lower hS hT hA hB hpos
          u.component u.tower u.state u.mem u.plot u.directions t ω i hi hk]
        let v : Fin (ω.1.partSize i) → (AnnularState S × ℝ) :=
          fun j => u.plot (u.directions (ω.1.emb i j))
        have hjet := hbound (ω.1.partSize i) hk (ω.1.partSize_pos i)
          b hb u.component u.tower
          (rootCosinePath (C.left u.component) (C.right u.component)
            (circleFlowCompactTime 0 Real.pi t))
          (rootCosinePath_mem_Icc (hA.2.2.1.1 u.component).2.1.le
            (circleFlowCompactTime 0 Real.pi t)) θ u.state u.mem v
        have hsum : 0 ≤ ∑ j, p high (u.plot (u.directions j)) :=
          Finset.sum_nonneg (fun j _ => apply_nonneg _ _)
        have hselected :
            oneHighVariationWeight p base high (u.state - (C.referenceState, 0)) v ≤
              ((N : ℝ) + 1) * R := by
          have hs := oneHighVariationWeight_le_selectedAggregate p base high
            (u.state - (C.referenceState, 0)) v
            (fun j => u.plot (u.directions j))
            (fun j => u.unit (ω.1.emb i j))
            (fun j => Finset.single_le_sum (fun l _ => apply_nonneg _ _)
              (Finset.mem_univ (ω.1.emb i j)))
          exact hs.trans (mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.add_le_add_right hk.le 1)
            (zero_le_one.trans hR))
        have hsample := materialSample_mem_radialCore hT
          hA.1.1.choose_spec.2.1 (C.cell u.component)
        have hw : B * T.H (T.sample (C.cell u.component)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell u.component)) ^ B ≤ B * Q := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left (hweight _ hsample) hBpos.le
        calc
          _ ≤ B * T.H (T.sample (C.cell u.component)) ^ (3 / 4 : ℝ) *
              T.E0 (T.sample (C.cell u.component)) ^ B *
                oneHighVariationWeight p base high (u.state - (C.referenceState, 0)) v :=
            hjet
          _ ≤ (B * Q) * (((N : ℝ) + 1) * R) :=
            mul_le_mul hw hselected
              (oneHighVariationWeight_nonneg p base high _ v) (mul_nonneg hBpos.le hQ.le)
          _ = (B * Q * ((N : ℝ) + 1)) * R := by ring
          _ ≤ M * R := mul_le_mul_of_nonneg_right (le_max_right _ _)
            (zero_le_one.trans hR)
      · rw [ordinaryFlowForcingFactorJet_large hS hT hA hB hpos
          u.component u.tower u.state u.mem u.plot u.directions t ω i hi
          (Nat.le_of_not_gt hk), abs_zero]
        exact mul_nonneg hM.le (zero_le_one.trans hR)
  have hs := circle_sobolevNorm_le_pointwiseJetBounds
    (ordinaryFlowForcingFactorJet hS hT hA hB hpos u.component u.tower
      u.state u.mem u.plot u.directions t ω i.succ)
    (periodicCircleJet_hasDerivAt _ _ _) s
    (mul_nonneg hM.le (zero_le_one.trans hR))
    (mul_nonneg hM.le (zero_le_one.trans hR))
    (hpoint 0 (Nat.zero_le s)) (hpoint s le_rfl)
  calc
    _ ≤ (2 : ℝ) ^ s * (M * R + M * R) := hs
    _ = _ := by rw [pow_succ]; ring

end ContinuousFlexibility.Blueprint
