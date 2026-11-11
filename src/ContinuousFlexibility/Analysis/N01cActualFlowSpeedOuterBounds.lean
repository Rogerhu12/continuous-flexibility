import ContinuousFlexibility.Analysis.N01cActualFlowCircleData
import ContinuousFlexibility.Analysis.N01cFlowVariationForcingBounds
import ContinuousFlexibility.Analysis.N01cCosineSpeedPrefixBounds
import ContinuousFlexibility.Analysis.N01cSpeedLowBounds

/-!
# Weighted Sobolev bounds for the actual outer forcing speed

Before composition with the trajectory, the selected speed factor has
the original material height factor and one aggregate high seminorm.
The state selection consists only of original parameter directions or
zeros. The fixed compact time change contributes one bounded derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem exists_circleFlowCompactTime_deriv_bound (a b : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      |deriv (circleFlowCompactTime a b) t| ≤ M := by
  have hc : Continuous (deriv (circleFlowCompactTime a b)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_circleFlowCompactTime a b)).2.continuous
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 1 M, zero_lt_one.trans_le (le_max_left _ _), fun t ht => ?_⟩
  have ht' : |deriv (circleFlowCompactTime a b) t| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM t ht
  exact ht'.trans (le_max_right _ _)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

section OuterField

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
  (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
    r ∈ Icc (C.left i) (C.right i) →
      0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
  (m : ℕ) {d : ℕ} (x : AnnularState S × ℝ)
  (hx : x ∈ stateNeighborhood S C base ε)
  (L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ))

/-- The selected mixed speed jet before its angle is composed with the flow. -/
def ordinaryFlowSpeedOuterField {N : ℕ} (v : Fin N → (Fin d → ℝ))
    (t : ℝ) (ω : FlowForcingChoice N) (θ : ℝ) : ℝ :=
  flowSpeedJointField
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L))
    ω.1.length 0
    (fun i => if i ∈ ω.2 then
      ((flowParameterIdentityJet (ω.1.partSize i) (v ∘ ω.1.emb i)).1, 0) else (0, 1))
    (t, θ)

theorem contDiff_ordinaryFlowSpeedOuterField {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (ω : FlowForcingChoice N) :
    ContDiff ℝ ∞ (ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t ω) :=
  (contDiff_flowSpeedJointField _
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L) ω.1.length 0 _).comp
      (contDiff_const.prodMk contDiff_id)

theorem ordinaryFlowSpeedOuterField_periodic {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (ω : FlowForcingChoice N) :
    Function.Periodic
      (ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t ω) Real.pi :=
  flowSpeedJointField_periodic _
    (ordinaryFlowFiniteSpeed_periodic hS hT hA hB hpos m x hx L) ω.1.length 0 _ t

def ordinaryFlowSpeedOuterJet {N : ℕ} (v : Fin N → (Fin d → ℝ))
    (t : ℝ) (ω : FlowForcingChoice N) (b : ℕ) : C(AddCircle Real.pi, ℝ) :=
  periodicCircleJet (ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t ω)
    (ordinaryFlowSpeedOuterField_periodic hS hT hA hB hpos m x hx L v t ω)
    (contDiff_ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t ω) b

theorem ordinaryFlowSpeedOuterJet_coe_apply {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (ω : FlowForcingChoice N)
    (b : ℕ) (θ : ℝ) :
    ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L v t ω b
      (θ : AddCircle Real.pi) =
        iteratedDeriv b (ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t ω) θ :=
  periodicCircleJet_coe_apply _ _ _ b θ

/-- The exact state-and-angle arity of every angular derivative of this
outer factor is read from the original forcing selection. -/
theorem ordinaryFlowSpeedOuterJet_eq_stateJet
    (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m))
    {N : ℕ} (v : Fin N → (Fin d → ℝ)) (t : ℝ) (ω : FlowForcingChoice N)
    (b : ℕ) (θ : ℝ) :
    ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L v t ω b
        (θ : AddCircle Real.pi) =
      deriv (circleFlowCompactTime 0 Real.pi) t *
        (smoothDirections_angularStateSlice (J.jet (circleFlowCompactTime 0 Real.pi t))
          (ω.stateWord.angleArity + b) θ).D ω.stateWord.stateArity x
            (flowForcingStateDirections ω L v) := by
  classical
  rw [ordinaryFlowSpeedOuterJet_coe_apply]
  have he : ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t ω =
      fun η => deriv (circleFlowCompactTime 0 Real.pi) t *
        J.D ω.1.length (x, (circleFlowCompactTime 0 Real.pi t, η))
          (fun i => flowStateAngleMap L (if i ∈ ω.2 then
            ((flowParameterIdentityJet (ω.1.partSize i) (v ∘ ω.1.emb i)).1, 0)
            else (0, 1))) := by
    funext η
    exact ordinaryFlowFiniteSpeedTower_D_apply hS hT hA hB hpos m J x hx L
      ω.1.length t η _
  rw [he, iteratedDeriv_const_mul_field]
  apply congrArg (fun y : ℝ => deriv (circleFlowCompactTime 0 Real.pi) t * y)
  have hslots :
      (fun i => flowStateAngleMap L (if i ∈ ω.2 then
        ((flowParameterIdentityJet (ω.1.partSize i) (v ∘ ω.1.emb i)).1, 0)
        else (0, 1))) =
      fun i => if decide (i ∈ ω.2) then
        (L ((flowParameterIdentityJet (ω.1.partSize i) (v ∘ ω.1.emb i)).1), 0)
        else (0, 1) := by
    funext i
    by_cases hi : i ∈ ω.2 <;> simp [hi, flowStateAngleMap_apply]
  rw [hslots]
  exact iteratedDeriv_joint_selectedSlots (J.jet (circleFlowCompactTime 0 Real.pi t))
    (fun b θ => smoothDirections_angularStateSlice
      (J.jet (circleFlowCompactTime 0 Real.pi t)) b θ)
    (fun i => decide (i ∈ ω.2)) b hx θ
    (fun i => L ((flowParameterIdentityJet (ω.1.partSize i) (v ∘ ω.1.emb i)).1))

end OuterField

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Blueprint

open Set MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- A weighted Sobolev bound on the original unit ball for every selected
outer speed factor. Its additive loss depends only on the state order N. -/
theorem n01_ordinaryFlowSpeedOuter_sobolev_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∀ N : ℕ, 0 < N → ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m, ∀ J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
        (componentCosineSpeed D S C m),
      ∀ d : ℕ, ∀ x : AnnularState S × ℝ, ∀ hx : x ∈ stateNeighborhood S C base ε,
      ∀ L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ), ∀ v : Fin N → (Fin d → ℝ),
      (∀ i, pairGrading (stateGrading S) realGrading base (L (v i)) ≤ 1) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω : FlowForcingChoice N,
        circleRealSobolevNorm (s : ℝ)
          (ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L v t ω 0) ≤
            B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              T.E0 (T.sample (C.cell m)) ^ B *
              ((1 + pairGrading (stateGrading S) realGrading (s + loss + offset)
                (x - (C.referenceState, 0))) +
                ∑ i, pairGrading (stateGrading S) realGrading (s + loss + offset) (L (v i))) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  obtain ⟨Mτ, hMτ, hτbound⟩ := exists_circleFlowCompactTime_deriv_bound 0 Real.pi
  intro N hN
  obtain ⟨offset, hbound⟩ :=
    n01_componentCosineAngularStateJets_prefix_bounds hS hT hA hε hB hE hSpeed N
  refine ⟨offset, fun s => ?_⟩
  obtain ⟨B, hBpos, hBbound⟩ := hbound s
  obtain ⟨C₀, hC₀, hweight⟩ := exists_sameConstant_materialWeight_bound
    ((2 : ℝ) ^ (s + 1) * Mτ * ((N : ℝ) + 1) * B) B (3 / 4 : ℝ)
  refine ⟨C₀, hC₀, ?_⟩
  intro m J d x hx L v hv t ht ω
  let p := pairGrading (stateGrading S) realGrading
  let high := s + loss + offset
  let R := (1 + p high (x - (C.referenceState, 0))) + ∑ i, p high (L (v i))
  let W := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ B
  have hsample := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  have hH := (hT.2.1 _ hsample).2.1.le
  have hE0 := hE _ hsample
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))
  have hW : 0 ≤ W :=
    mul_nonneg (mul_nonneg hBpos.le (Real.rpow_nonneg hH _))
      (Real.rpow_nonneg (zero_le_one.trans hE0) _)
  have hk := flowForcingStateDirections_stateArity_le ω
  have harity := ω.stateWord.arity_sum
  have hlen := ω.1.length_le
  have hlenpos := ω.1.length_pos hN
  have hτ := circleFlowCompactTime_mem Real.pi_pos.le t
  have hselectedLow := flowForcingStateDirections_seminorm_le ω L v (p base)
    (by norm_num : (0 : ℝ) ≤ 1) hv
  have hsum : 0 ≤ ∑ i, p high (L (v i)) :=
    Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
  have hselectedHigh := flowForcingStateDirections_seminorm_le ω L v (p high) hsum
    (fun i => Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i))
  have hselected : oneHighVariationWeight p base high (x - (C.referenceState, 0))
      (flowForcingStateDirections ω L v) ≤ ((N : ℝ) + 1) * R :=
    (oneHighVariationWeight_le_selectedAggregate p base high (x - (C.referenceState, 0))
      (flowForcingStateDirections ω L v) (fun i => L (v i)) hselectedLow hselectedHigh).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hk 1) hR)
  have hpoint (b : ℕ) (hb : b ≤ s) (θ : ℝ) :
      |ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L v t ω b
        (θ : AddCircle Real.pi)| ≤ Mτ * W * ((N : ℝ) + 1) * R := by
    rw [ordinaryFlowSpeedOuterJet_eq_stateJet hS hT hA hB hpos m x hx L J,
      abs_mul]
    have hraw := hBbound ω.stateWord.stateArity hk m (ω.stateWord.angleArity + b)
      (circleFlowCompactTime 0 Real.pi t) θ (by omega) hτ (by omega)
      (smoothDirections_angularStateSlice (J.jet (circleFlowCompactTime 0 Real.pi t))
        (ω.stateWord.angleArity + b) θ) x hx (flowForcingStateDirections ω L v)
    have hjet : |(smoothDirections_angularStateSlice
        (J.jet (circleFlowCompactTime 0 Real.pi t)) (ω.stateWord.angleArity + b) θ).D ω.stateWord.stateArity x (flowForcingStateDirections ω L v)| ≤
        W * (((N : ℝ) + 1) * R) :=
      hraw.trans (mul_le_mul_of_nonneg_left hselected hW)
    calc
      _ ≤ Mτ * (W * (((N : ℝ) + 1) * R)) :=
        mul_le_mul (hτbound t ht) hjet (abs_nonneg _) hMτ.le
      _ = _ := by ring
  have hnorm := circle_sobolevNorm_le_pointwiseJetBounds
    (ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L v t ω)
    (periodicCircleJet_hasDerivAt _ _ _) s
    (by positivity : 0 ≤ Mτ * W * ((N : ℝ) + 1) * R)
    (by positivity : 0 ≤ Mτ * W * ((N : ℝ) + 1) * R)
    (hpoint 0 (Nat.zero_le s)) (hpoint s le_rfl)
  calc
    _ ≤ (2 : ℝ) ^ s * ((Mτ * W * ((N : ℝ) + 1) * R) +
        Mτ * W * ((N : ℝ) + 1) * R) := hnorm
    _ = ((2 : ℝ) ^ (s + 1) * Mτ * ((N : ℝ) + 1) * B) *
        T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B * R := by
      dsimp only [W]
      rw [pow_succ]
      ring
    _ ≤ _ := hweight _ _ _ hH hE0 hR

end ContinuousFlexibility.Blueprint
