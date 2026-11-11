import ContinuousFlexibility.Analysis.ControlCellEndpointBounds
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Scalar.WeightedReferenceBounds

/-!
# Actual N01 coefficient towers with uniform spatial bounds

The sampled height decay absorbs every fixed coefficient-envelope power.
The pointwise N01 towers therefore have one constant over the entire
annulus, with the same parameter base and loss. Near either endpoint one
positive power of the actual material height weight remains available.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

local instance n07aForwardCoefficientsInst1 (S : PhysicalSpacesData) : AddCommGroup (AnnularState S) := inferInstance
local instance n07aForwardCoefficientsInst2 (S : PhysicalSpacesData) : Module ℝ (AnnularState S) := inferInstance
local instance n07aForwardCoefficientsInst3 (S : PhysicalSpacesData) : TopologicalSpace (AnnularState S) := inferInstance
local instance n07aForwardCoefficientsInst4 (S : PhysicalSpacesData) : AddGroup (AnnularState S) :=
  (inferInstance : AddCommGroup (AnnularState S)).toAddGroup
local instance n07aForwardCoefficientsInst5 (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (inferInstance : Module ℝ (AnnularState S)).toSMul
local instance n07aForwardCoefficientsInst6 (S : PhysicalSpacesData) : Sub (AnnularState S) :=
  (inferInstance : AddCommGroup (AnnularState S)).toSub

/-- The actual sum grading evaluated as a real number. Naming its value
avoids repeating scalar-action instance comparisons in coefficient bounds. -/
def n07aRawParameterSize (S : PhysicalSpacesData) (s : ℕ)
    (z : AnnularState S × ℝ) : ℝ :=
  stateGrading S s z.1 + |z.2|

theorem n07aRawParameterSize_eq (S : PhysicalSpacesData) (s : ℕ)
    (z : AnnularState S × ℝ) :
    pairGrading (stateGrading S) realGrading s z = n07aRawParameterSize S s z := rfl

/-- The exact one-high-variation expression of N01, in numeric form. -/
def n07aRawParameterVariation (S : PhysicalSpacesData) (base high : ℕ)
    (z : AnnularState S × ℝ) {k : ℕ} (v : Fin k → (AnnularState S × ℝ)) : ℝ :=
  (1 + n07aRawParameterSize S high z) * ∏ i, n07aRawParameterSize S base (v i) +
    ∑ i : Fin k, n07aRawParameterSize S high (v i) *
      ∏ j ∈ Finset.univ.erase i, n07aRawParameterSize S base (v j)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}


/-- A positive material height power dominates every fixed `E0` power at
all actual samples, with one constant chosen before the sample index. -/
theorem n07a_materialSample_envelope_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A ≤ K := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, hH, _⟩ := hdata
  obtain ⟨C, hC, hCb⟩ := hE A
  obtain ⟨B, hB, hBb, _⟩ := hH 1 γ hγ
  refine ⟨C * B, mul_pos hC hB, fun m => ?_⟩
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 m
  have hpos := (hT.2.1 _ hm).2.1
  calc
    T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A ≤
        T.H (T.sample m) ^ γ * (C * T.M (T.sample m)) :=
      mul_le_mul_of_nonneg_left (hCb _ hm) (Real.rpow_pos_of_pos hpos _).le
    _ = C * (T.H (T.sample m) ^ γ * T.M (T.sample m)) := by ring
    _ ≤ C * B := mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_one] using hBb _ hm) hC.le

variable {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}


private def n07aSampleCoefficientBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (k s : ℕ) (B : ℝ) : Prop :=
  ∀ (m : ℕ) (i : Fin 3) (a b : ℕ) (p : PolarPoint),
    a + b ≤ s → p.1 ∈ D.cells m →
    ∃ J : SmoothDirections (E := AnnularState S × ℝ) (F := ℝ)
      (stateNeighborhood S C base ε) (coefficientFamily D S C i a b p),
      ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
        ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          oneHighVariationWeight (E := AnnularState S × ℝ)
            (pairGrading (E := AnnularState S) (F := ℝ) (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v

private theorem n07a_sample_coefficient_bound
    (h01 : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ n07aSampleCoefficientBound D T S C base loss ε k s B :=
  h01.2.2.2.2.2.2.2.2.2.2.2.1 k s

/-- The actual N01 coefficient jet towers admit spatially uniform bounds;
the fixed parameter loss is unchanged. -/
theorem n07a_coefficientFamily_uniform_tower_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin 3) (a b : ℕ) (p : PolarPoint),
      a + b ≤ s → p ∈ annularOpen D →
      ∃ J : SmoothDirections (E := AnnularState S × ℝ) (F := ℝ) (stateNeighborhood S C base ε)
          (coefficientFamily D S C i a b p),
        ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
          ∀ v : Fin k → (AnnularState S × ℝ),
          |J.D k z v| ≤ K *
            n07aRawParameterVariation S
              base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
  have hD := h01.1
  let bound := n07a_sample_coefficient_bound h01 k s
  let B : ℝ := bound.choose
  have hB : 0 < B := bound.choose_spec.1
  have hBj : n07aSampleCoefficientBound D T S C base loss ε k s B := bound.choose_spec.2
  let envelope := n07a_materialSample_envelope_bound hD.1 hT
    (by norm_num : (0 : ℝ) < 3 / 4) B
  let K : ℝ := envelope.choose
  have hK : 0 < K := envelope.choose_spec.1
  have hKb : ∀ m, T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B ≤ K :=
    envelope.choose_spec.2
  refine ⟨B * K, mul_pos hB hK, fun i a b p hab hp => ?_⟩
  let cell := hD.1.choose_spec.2.1.exists_cell hp.1
  let m : ℕ := cell.choose
  have hpm : p.1 ∈ D.cells m := cell.choose_spec
  let J := (hBj m i a b p hab hpm).choose
  have hJ := (hBj m i a b p hab hpm).choose_spec
  refine ⟨J, fun z hz v => ?_⟩
  have hv : 0 ≤ n07aRawParameterVariation S
      base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
    unfold n07aRawParameterVariation n07aRawParameterSize
    positivity
  calc
    |J.D k z v| ≤ (B *
        (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B)) *
        n07aRawParameterVariation S
          base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
      simpa only [J, oneHighVariationWeight, n07aRawParameterSize_eq,
        n07aRawParameterVariation, mul_assoc] using hJ z hz v
    _ ≤ (B * K) *
        n07aRawParameterVariation S
          base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hKb m) hB.le) hv

/-- One endpoint collar works for all three coefficients and all spatial
jets up to the chosen order; it is shared by both annular ends. -/
theorem n07a_coefficientFamily_endpoint_tower_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k s : ℕ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ (i : Fin 3) (a b : ℕ) (p : PolarPoint), a + b ≤ s →
      p ∈ annularOpen D → Statements.endpointDistance D p.1 < δ →
      ∃ J : SmoothDirections (E := AnnularState S × ℝ) (F := ℝ) (stateNeighborhood S C base ε)
          (coefficientFamily D S C i a b p),
        ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
          ∀ v : Fin k → (AnnularState S × ℝ),
          |J.D k z v| ≤ K * T.H p.1 ^ (3 / 64 : ℝ) *
            n07aRawParameterVariation S
              base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
  have hD := h01.1
  let bound := n07a_sample_coefficient_bound h01 k s
  let B : ℝ := bound.choose
  have hB : 0 < B := bound.choose_spec.1
  have hBj : n07aSampleCoefficientBound D T S C base loss ε k s B := bound.choose_spec.2
  let envelope := materialSample_endpoint_weight_bound hT hD.1
    (by norm_num : (0 : ℝ) < 3 / 4) B (B := 0) le_rfl
  let δ : ℝ := envelope.choose
  let K : ℝ := envelope.choose_spec.choose
  have hδ : 0 < δ := envelope.choose_spec.choose_spec.1
  have hK : 0 < K := envelope.choose_spec.choose_spec.2.1
  have hKb : ∀ (i j : ℕ) (r : ℝ), r ∈ Ioo D.a D.b → r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ 0 →
      Statements.endpointDistance D r < δ →
      T.H (T.sample i) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B ≤
        K * T.H r ^ ((3 / 4 : ℝ) / 16) := envelope.choose_spec.choose_spec.2.2
  refine ⟨δ, B * K, hδ, mul_pos hB hK, fun i a b p hab hp hnear => ?_⟩
  let cell := hD.1.choose_spec.2.1.exists_cell hp.1
  let m : ℕ := cell.choose
  have hpm : p.1 ∈ D.cells m := cell.choose_spec
  let J := (hBj m i a b p hab hpm).choose
  have hJ := (hBj m i a b p hab hpm).choose_spec
  refine ⟨J, fun z hz v => ?_⟩
  have hv : 0 ≤ n07aRawParameterVariation S
      base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
    unfold n07aRawParameterVariation n07aRawParameterSize
    positivity
  have hdecay : T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B ≤
      K * T.H p.1 ^ (3 / 64 : ℝ) := by
    convert hKb m m p.1 hp.1 hpm (by simp only [sub_self, abs_zero, le_refl]) hnear
      using 1 <;> norm_num
  calc
    |J.D k z v| ≤ (B *
        (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B)) *
        n07aRawParameterVariation S
          base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
      simpa only [J, oneHighVariationWeight, n07aRawParameterSize_eq,
        n07aRawParameterVariation, mul_assoc] using hJ z hz v
    _ ≤ (B * (K * T.H p.1 ^ (3 / 64 : ℝ))) *
        n07aRawParameterVariation S
          base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hB.le) hv
    _ = _ := by ring

/-- Fix one genuine tower for each actual spatial coefficient jet.  Its
choice is independent of the parameter order and the requested bound. -/
def n07aCoefficientTower
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (i : Fin 3) (a b : ℕ) (p : annularOpen D) :
    SmoothDirections (E := AnnularState S × ℝ) (F := ℝ) (stateNeighborhood S C base ε)
      (coefficientFamily D S C i a b p.val) :=
  ((n07a_coefficientFamily_uniform_tower_bound hT h01 0 (a + b)).choose_spec.2
    i a b p.val le_rfl p.property).choose

theorem n07aCoefficientTower_unique
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (i : Fin 3) (a b : ℕ) (p : annularOpen D)
    (J : SmoothDirections (E := AnnularState S × ℝ) (F := ℝ) (stateNeighborhood S C base ε)
      (coefficientFamily D S C i a b p.val))
    (k : ℕ) {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    (n07aCoefficientTower hT h01 i a b p).D k z = J.D k z :=
  HasProjectiveJetsOn.unique J.open_domain
    (n07aCoefficientTower hT h01 i a b p).hasProjectiveJetsOn
    J.hasProjectiveJetsOn k z hz

/-- All parameter orders and all requested spatial orders estimate the
same chosen tower, by uniqueness of genuine directional derivatives. -/
theorem n07aCoefficientTower_uniform_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin 3) (a b : ℕ) (p : annularOpen D),
      a + b ≤ s → ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |(n07aCoefficientTower hT h01 i a b p).D k z v| ≤ K *
          n07aRawParameterVariation S
            base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
  let bound := n07a_coefficientFamily_uniform_tower_bound hT h01 k s
  let K : ℝ := bound.choose
  have hK : 0 < K := bound.choose_spec.1
  have hbound := bound.choose_spec.2
  refine ⟨K, hK, fun i a b p hab z hz v => ?_⟩
  let J := (hbound i a b p.val hab p.property).choose
  have hJ := (hbound i a b p.val hab p.property).choose_spec
  rw [n07aCoefficientTower_unique hT h01 i a b p J k hz]
  exact hJ z hz v

/-- The zeroth parameter jet is the real mixed spatial derivative of the
coefficient difference, so its uniform estimate needs no auxiliary tower. -/
theorem n07a_coefficientFamily_uniform_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin 3) (a b : ℕ) (p : PolarPoint),
      a + b ≤ s → p ∈ annularOpen D →
      ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
        |coefficientFamily D S C i a b p z| ≤ K *
          (1 + n07aRawParameterSize S (s + loss)
            (z - (C.referenceState, 0) : AnnularState S × ℝ)) := by
  let bound := n07aCoefficientTower_uniform_bound hT h01 0 s
  let K : ℝ := bound.choose
  have hK : 0 < K := bound.choose_spec.1
  have hbound := bound.choose_spec.2
  refine ⟨K, hK, fun i a b p hab hp z hz => ?_⟩
  have h := hbound i a b ⟨p, hp⟩ hab z hz Fin.elim0
  rw [(n07aCoefficientTower hT h01 i a b ⟨p, hp⟩).zero z hz] at h
  simpa only [K, n07aRawParameterVariation, Fin.prod_univ_zero,
    Fin.sum_univ_zero, mul_one, add_zero] using h

/-- The same chosen tower has genuine decay at both ends of the annulus. -/
theorem n07aCoefficientTower_endpoint_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k s : ℕ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ (i : Fin 3) (a b : ℕ) (p : annularOpen D), a + b ≤ s →
      Statements.endpointDistance D p.val.1 < δ →
      ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |(n07aCoefficientTower hT h01 i a b p).D k z v| ≤
          K * T.H p.val.1 ^ (3 / 64 : ℝ) *
            n07aRawParameterVariation S
              base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
  let bound := n07a_coefficientFamily_endpoint_tower_bound hT h01 k s
  let δ : ℝ := bound.choose
  let K : ℝ := bound.choose_spec.choose
  have hδ : 0 < δ := bound.choose_spec.choose_spec.1
  have hK : 0 < K := bound.choose_spec.choose_spec.2.1
  have hbound := bound.choose_spec.choose_spec.2.2
  refine ⟨δ, K, hδ, hK, fun i a b p hab hnear z hz v => ?_⟩
  let J := (hbound i a b p.val hab p.property hnear).choose
  have hJ := (hbound i a b p.val hab p.property hnear).choose_spec
  rw [n07aCoefficientTower_unique hT h01 i a b p J k hz]
  exact hJ z hz v

/-- The endpoint decay becomes a global bound by compactness of the
remaining physical interval. This supplies one integrable spatial
majorant for every fixed order of the same genuine coefficient tower. -/
theorem n07aCoefficientTower_decay_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (k s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin 3) (a b : ℕ) (p : annularOpen D),
      a + b ≤ s → ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |(n07aCoefficientTower hT h01 i a b p).D k z v| ≤
          K * T.H p.val.1 ^ (3 / 64 : ℝ) *
            n07aRawParameterVariation S
              base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
  let uniform := n07aCoefficientTower_uniform_bound hT h01 k s
  let U : ℝ := uniform.choose
  have hU : 0 < U := uniform.choose_spec.1
  have hUb := uniform.choose_spec.2
  let endpoint := n07aCoefficientTower_endpoint_bound hT h01 k s
  let δ : ℝ := endpoint.choose
  let V : ℝ := endpoint.choose_spec.choose
  have hδ : 0 < δ := endpoint.choose_spec.choose_spec.1
  have hV : 0 < V := endpoint.choose_spec.choose_spec.2.1
  have hVb := endpoint.choose_spec.choose_spec.2.2
  let I : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hI : I ⊆ Ioo D.a D.b := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hcont : ContinuousOn (fun r : ℝ => T.H r ^ (-(3 / 64 : ℝ))) I :=
    (((hT.1 T.H (by simp)).rpow_const_of_ne
      (fun r hr => (hT.2.1 r hr).2.1.ne')).continuousOn).mono hI
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hcont
  let K : ℝ := V + U * max B 0
  have hK : 0 < K := add_pos_of_pos_of_nonneg hV
    (mul_nonneg hU.le (le_max_right B 0))
  refine ⟨K, hK, fun i a b p hab z hz v => ?_⟩
  have hH : 0 < T.H p.val.1 := (hT.2.1 p.val.1 p.property.1).2.1
  have hHpow : 0 ≤ T.H p.val.1 ^ (3 / 64 : ℝ) := Real.rpow_nonneg hH.le _
  have hv : 0 ≤ n07aRawParameterVariation S
      base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
    unfold n07aRawParameterVariation n07aRawParameterSize
    positivity
  by_cases hnear : Statements.endpointDistance D p.val.1 < δ
  · exact (hVb i a b p hab hnear z hz v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (mul_nonneg hU.le (le_max_right B 0))) hHpow) hv)
  have hpI : p.val.1 ∈ I := by
    have hdist : δ ≤ min (p.val.1 - D.a) (D.b - p.val.1) := le_of_not_gt hnear
    have hleft := hdist.trans (min_le_left _ _)
    have hright := hdist.trans (min_le_right _ _)
    exact ⟨by linarith only [hleft], by linarith only [hright]⟩
  have hBpow : T.H p.val.1 ^ (-(3 / 64 : ℝ)) ≤ max B 0 :=
    (hB ⟨p.val.1, hpI, rfl⟩).trans (le_max_left B 0)
  have hone : (1 : ℝ) ≤ max B 0 * T.H p.val.1 ^ (3 / 64 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hBpow hHpow
    simpa only [← Real.rpow_add hH, neg_add_cancel, Real.rpow_zero] using h
  have hUK : U ≤ K * T.H p.val.1 ^ (3 / 64 : ℝ) := by
    calc
      U = U * 1 := (mul_one U).symm
      _ ≤ U * (max B 0 * T.H p.val.1 ^ (3 / 64 : ℝ)) :=
        mul_le_mul_of_nonneg_left hone hU.le
      _ = (U * max B 0) * T.H p.val.1 ^ (3 / 64 : ℝ) := (mul_assoc _ _ _).symm
      _ ≤ K * T.H p.val.1 ^ (3 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hV.le) hHpow
  exact (hUb i a b p hab z hz v).trans (mul_le_mul_of_nonneg_right hUK hv)

/-- The genuine zeroth jet supplies the same global height decay for the
actual coefficient differences themselves. -/
theorem n07a_coefficientFamily_decay_bound
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin 3) (a b : ℕ) (p : PolarPoint),
      a + b ≤ s → p ∈ annularOpen D →
      ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
        |coefficientFamily D S C i a b p z| ≤ K * T.H p.1 ^ (3 / 64 : ℝ) *
          (1 + n07aRawParameterSize S (s + loss)
            (z - (C.referenceState, 0) : AnnularState S × ℝ)) := by
  let bound := n07aCoefficientTower_decay_bound hT h01 0 s
  let K : ℝ := bound.choose
  have hK : 0 < K := bound.choose_spec.1
  have hbound := bound.choose_spec.2
  refine ⟨K, hK, fun i a b p hab hp z hz => ?_⟩
  have h := hbound i a b ⟨p, hp⟩ hab z hz Fin.elim0
  rw [(n07aCoefficientTower hT h01 i a b ⟨p, hp⟩).zero z hz] at h
  simpa only [K, n07aRawParameterVariation, Fin.prod_univ_zero,
    Fin.sum_univ_zero, mul_one, add_zero] using h

end ContinuousFlexibility.Analysis
