import ContinuousFlexibility.Analysis.CoupledScalarErrorCoefficient

/-!
# One smooth tame sector neighborhood for the actual error coefficient

The input logarithm is linear after translation by the reference state.
The common height is affine and the external parameter is a coordinate.
Finite algebra of the actual weak-height operations therefore gives one
uniform tower, which is restricted to a sector neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem coupled_subtype_first_isTame
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (W : Submodule ℝ E) (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    IsTameLinear (pairGrading (fun n => (p n).comp W.subtype) q) p
      (W.subtypeL.comp (ContinuousLinearMap.fst ℝ W F)).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun z => ?_⟩
  change p s z.1.val ≤ (1 : ℝ) * (p (s + 0) z.1.val + q (s + 0) z.2)
  simpa only [Nat.add_zero, one_mul] using
    (le_add_of_nonneg_right (apply_nonneg (q s) z.2) :
      p s z.1.val ≤ p s z.1.val + q s z.2)

private theorem coupled_linear_translate_zero
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (L : E →L[ℝ] F) {a : E} (ha : L a = 0) (x : E) :
    L (a + x) = L x := by
  simpa only [ha, zero_add] using L.map_add a x

def coupledSectorStateCLM (S : PhysicalSpacesData) :
    (StateDirections S × ℝ) →L[ℝ] AnnularState S :=
  (stateSectorSubmodule S).subtypeL.comp (ContinuousLinearMap.fst ℝ (StateDirections S) ℝ)

theorem coupledSectorStateCLM_apply (S : PhysicalSpacesData) (z : StateDirections S × ℝ) :
    coupledSectorStateCLM S z = z.1.val := rfl

theorem coupledSectorStateCLM_isTame (S : PhysicalSpacesData) :
    IsTameLinear (pairGrading (sectorGrading S) realGrading) (stateGrading S)
      (coupledSectorStateCLM S).toLinearMap 0 0 :=
  coupled_subtype_first_isTame (stateSectorSubmodule S) (stateGrading S) realGrading

def coupledStateHeightCoordinateCLM (S : PhysicalSpacesData) :
    AnnularState S →L[ℝ] HeightPair S :=
  ContinuousLinearMap.fst ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))

theorem coupledStateHeightCoordinateCLM_isTame (S : PhysicalSpacesData) :
    IsTameLinear (stateGrading S) (heightPairGrading S)
      (coupledStateHeightCoordinateCLM S).toLinearMap 0 0 :=
  scalar_pair_fst_isTame (heightPairGrading S)
    (pairGrading realGrading (pairGrading (S.circle (3 / 4 : ℝ)).grading
      (S.circle (3 / 4 : ℝ)).grading))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem coupledLogProfileLift_liftSector
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (z : StateDirections S × ℝ) :
    coupledLogProfileLift hT hS hN (liftSectorParameter S C z).1 =
      coupledLogProfileLift hT hS hN z.1.val :=
  coupled_linear_translate_zero (coupledLogProfileLift hT hS hN)
    (coupledLogProfileLift_reference hT hS hN) z.1.val

theorem coupledScalarErrorCoefficient_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    UniformTameGerm (pairGrading (sectorGrading S) realGrading) (coupledWeakHeightGrading S)
      (0 : StateDirections S × ℝ)
      (fun z => coupledScalarErrorCoefficient hT hS hN (liftSectorParameter S C z)) := by
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p :=
    pairGrading_monotone (solve_sectorGrading_monotone S) weighted_realGrading_monotone
  have ht : WithSeminorms p :=
    withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
      weighted_realGrading_withSeminorms
  let l : (StateDirections S × ℝ) → CoupledWeakHeight S :=
    fun z => coupledLogProfileLift hT hS hN (liftSectorParameter S C z).1
  let u : (StateDirections S × ℝ) → HeightPair S :=
    fun z => (liftSectorParameter S C z).1.1
  let q : (StateDirections S × ℝ) → ℝ := Prod.snd
  have hlLinear := uniformTameGerm_continuousLinear ht (0 : StateDirections S × ℝ)
    ((coupledLogProfileLift hT hS hN).comp (coupledSectorStateCLM S))
    ((coupledLogProfileLift_isTame hT hS hN).comp (coupledSectorStateCLM_isTame S))
  have hl : UniformTameGerm p (coupledWeakHeightGrading S) 0 l :=
    hlLinear.congr (fun z => (coupledLogProfileLift_liftSector hT hS hN z).symm)
  have hl0 : l 0 = 0 :=
    (coupledLogProfileLift_liftSector hT hS hN (0 : StateDirections S × ℝ)).trans
      (coupledLogProfileLift hT hS hN).map_zero
  have huLinear := uniformTameGerm_continuousLinear ht (0 : StateDirections S × ℝ)
    ((coupledStateHeightCoordinateCLM S).comp (coupledSectorStateCLM S))
    ((coupledStateHeightCoordinateCLM_isTame S).comp (coupledSectorStateCLM_isTame S))
  have huConst : UniformTameGerm p (heightPairGrading S) (0 : StateDirections S × ℝ)
      (fun _ => C.referenceState.1) := uniformTameGerm_const ht _ _
  have hu : UniformTameGerm p (heightPairGrading S) 0 u :=
    (huConst.add huLinear hp ht).congr (fun _ => rfl)
  have hq : UniformTameGerm p realGrading (0 : StateDirections S × ℝ) q :=
    uniformTameGerm_continuousLinear ht 0
      (ContinuousLinearMap.snd ℝ (StateDirections S) ℝ)
      (scalar_pair_snd_isTame (sectorGrading S) realGrading)
  have hd : UniformTameGerm p (coupledWeakHeightGrading S) 0
      (fun z => coupledActualQDefect hT hS hN (liftSectorParameter S C z)) :=
    hl.coupledWeakQDefect hl0 hu hq hN.1.1 hT hS hp ht
  have hd0 : coupledActualQDefect hT hS hN
      (liftSectorParameter S C (0 : StateDirections S × ℝ)) = 0 :=
    coupledWeakQDefect_zero_of_q hN.1.1 hT hS _ _
  exact hl.coupledWeakTypeCoefficient hl0 hd hd0 hN.1.1 hT hS hp ht

private theorem coupled_pair_real_grading_apply
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (n : ℕ) (z : E × ℝ) :
    pairGrading p realGrading n z = p n z.1 + |z.2| := by
  simp only [pairGrading, realGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, coe_normSeminorm, Real.norm_eq_abs]

/-- A single smaller sector neighborhood carries the actual coefficient tower. -/
theorem coupledScalarErrorCoefficient_smoothTameOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ b : ℕ, ∃ δ : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      SmoothTameOn (pairGrading (sectorGrading S) realGrading) (coupledWeakHeightGrading S)
        (sectorNeighborhood S b δ δ)
        (fun z => coupledScalarErrorCoefficient hT hS hN (liftSectorParameter S C z)) := by
  let hgerm := coupledScalarErrorCoefficient_uniformTameGerm hT hS hN
  let b : ℕ := hgerm.choose
  let hbase := hgerm.choose_spec
  let ell : ℕ := hbase.choose
  let hloss := hbase.choose_spec
  let τ : ℝ := hloss.choose
  have hτ : 0 < τ := hloss.choose_spec.1
  let hfixed := hloss.choose_spec.2
  have hδ : 0 < min ε (τ / 2) := lt_min hN.2.1 (half_pos hτ)
  refine ⟨max base b, min ε (τ / 2), le_max_left _ _, hδ, min_le_left _ _, ?_⟩
  apply (hfixed.restrict
    (coupled_sectorNeighborhood_isOpen S (max base b) (min ε (τ / 2)) (min ε (τ / 2))) ?_).1
  intro z hz
  change pairGrading (sectorGrading S) realGrading b (z - 0) < τ
  rw [sub_zero, coupled_pair_real_grading_apply]
  have h₁ : sectorGrading S b z.1 < τ / 2 :=
    (solve_sectorGrading_monotone S (le_max_right base b) z.1).trans_lt
      (hz.1.trans_le (min_le_right _ _))
  have h₂ : |z.2| < τ / 2 := hz.2.trans_le (min_le_right _ _)
  linarith only [h₁, h₂]

end ContinuousFlexibility.Statements
