import ContinuousFlexibility.Analysis.N01FlowStateLocality
import ContinuousFlexibility.Analysis.N01HeightPlateauDirections
import ContinuousFlexibility.Analysis.CircleJetPointwiseEnergy

/-!
# Actual component-local state directions and their physical energies

One localized direction consists of a physical plateau height and the
single constant circle control seen by that component. Its trace,
border and chart coordinates vanish. The same direction works in every
genuine parameter jet. Its weighted grading is controlled by the physical
plateau energy and the original control's circle component energy.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01LocalizedStateDirectionsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

private theorem seminorm_add_smul_bound {E : Type*}
    [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) (x y : E) (c A B : ℝ)
    (hx : p x = A) (hy : p y ≤ B) :
    p (x + c • y) ≤ A + |c| * B := by
  have ht : p (x + c • y) ≤ p x + |c| * p y := by
    simpa only [map_smul_eq_mul, Real.norm_eq_abs] using map_add_le_add p x (c • y)
  rw [hx] at ht
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy (abs_nonneg c)))

private theorem pairGrading_at_real_zero {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (s : ℕ) (x : E) :
    pairGrading p realGrading s (x, 0) = p s x := by
  rw [pairGrading_apply, map_zero, add_zero]

def controlParameterDirection
    {T : MaterialData} {S : PhysicalSpacesData}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) (m : ℕ) :
    StateDirections S × ℝ :=
  (⟨singletonKappaDirection hC m, singletonKappaDirection_sector hC m⟩, 0)

def localizedStateParameterDirection
    {T : MaterialData} {S : PhysicalSpacesData}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (m : ℕ) (η : HeightPair S) (c : ℝ) : StateDirections S × ℝ :=
  heightParameterDirection S η + c • controlParameterDirection hC m

theorem localizedStateParameterDirection_scalar
    {T : MaterialData} {S : PhysicalSpacesData}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (m : ℕ) (η : HeightPair S) (c : ℝ) :
    (localizedStateParameterDirection hC m η c).2 = 0 := by
  change (0 : ℝ) + c * 0 = 0
  rw [mul_zero, zero_add]

theorem localizedStateParameterDirection_height
    {T : MaterialData} {S : PhysicalSpacesData}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (m : ℕ) (η : HeightPair S) (c : ℝ) :
    (localizedStateParameterDirection hC m η c).1.val.1 = η := by
  change η + c • (0 : HeightPair S) = η
  rw [smul_zero, add_zero]

theorem localizedStateParameterDirection_control
    {T : MaterialData} {S : PhysicalSpacesData}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (m : ℕ) (η : HeightPair S) (c : ℝ) (n : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (localizedStateParameterDirection hC m η c).1.val.2.2.1 n θ =
      if n = m then c else 0 := by
  change (S.circle (3 / 4 : ℝ)).decode
    (0 + c • circleSingletonLinear hC m 1) n θ = _
  simp only [zero_add, map_smul, Pi.smul_apply, smul_eq_mul,
    circleSingletonLinear_decode, circleSingletonField]
  split_ifs <;> simp only [mul_one, mul_zero]

theorem controlParameterDirection_grading
    {T : MaterialData} {S : PhysicalSpacesData}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) (m s : ℕ) :
    pairGrading (sectorGrading S) realGrading s (controlParameterDirection hC m) =
      stateGrading S s (singletonKappaDirection hC m) := by
  exact pairGrading_at_real_zero (sectorGrading S) s
    (⟨singletonKappaDirection hC m, singletonKappaDirection_sector hC m⟩ : StateDirections S)

theorem localizedStateParameterDirection_grading_le
    {T : MaterialData} {S : PhysicalSpacesData}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (m s : ℕ) (η : HeightPair S) (c : ℝ)
    (hM : 1 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m)) :
    pairGrading (sectorGrading S) realGrading s
      (localizedStateParameterDirection hC m η c) ≤
      heightPairGrading S s η + |c| * circleSingletonGradingConstant s *
        (T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) := by
  have hcontrol : pairGrading (sectorGrading S) realGrading s (controlParameterDirection hC m) ≤
      circleSingletonGradingConstant s *
        (T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) :=
    (controlParameterDirection_grading hC m s).trans_le
      (singletonKappaDirection_grading_le hC m s hM hH)
  exact (seminorm_add_smul_bound (pairGrading (sectorGrading S) realGrading s)
    (heightParameterDirection S η) (controlParameterDirection hC m) c _ _
    (heightParameterDirection_grading S η s) hcontrol).trans_eq (by ring)

theorem localizedStateParameterDirection_weighted_grading_le
    {T : MaterialData} {S : PhysicalSpacesData}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (u : CircleSpace S) (m s d : ℕ) (η : HeightPair S)
    (hM : 1 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m)) :
    T.M (T.sample m) ^ d * pairGrading (sectorGrading S) realGrading s
      (localizedStateParameterDirection hC m η ((S.circle (3 / 4 : ℝ)).decode u m 0)) ≤
      T.M (T.sample m) ^ d * heightPairGrading S s η +
        (circleSingletonGradingConstant s * (2 * circleSobolevConstant)) *
          Real.sqrt (circleComponentEnergy T (3 / 4 : ℝ) (s + d + 1)
            ((S.circle (3 / 4 : ℝ)).decode u) m).toReal := by
  have hpoint := circleWeighted_abs_le_componentEnergy (hC.2.2.2.1 u)
    (zero_le_one.trans hM) hH (m := m) (a := 0) (b := s + d) (s := s + d + 1)
    (by omega) (0 : ℝ)
  simp only [iteratedDeriv_zero] at hpoint
  have hloc := localizedStateParameterDirection_grading_le hC m s η
    ((S.circle (3 / 4 : ℝ)).decode u m 0) hM hH
  calc
    _ ≤ T.M (T.sample m) ^ d *
        (heightPairGrading S s η +
          |(S.circle (3 / 4 : ℝ)).decode u m 0| * circleSingletonGradingConstant s *
            (T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-(3 / 4 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hloc (pow_nonneg (zero_le_one.trans hM) d)
    _ = T.M (T.sample m) ^ d * heightPairGrading S s η +
        circleSingletonGradingConstant s *
          ((T.M (T.sample m) ^ (s + d) * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
            |(S.circle (3 / 4 : ℝ)).decode u m 0|) := by rw [pow_add]; ring
    _ ≤ T.M (T.sample m) ^ d * heightPairGrading S s η +
        circleSingletonGradingConstant s *
          (2 * circleSobolevConstant * Real.sqrt
            (circleComponentEnergy T (3 / 4 : ℝ) (s + d + 1)
              ((S.circle (3 / 4 : ℝ)).decode u) m).toReal) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpoint
        (circleSingletonGradingConstant_nonneg s))
    _ = _ := by ring

attribute [local irreducible] localizedStateParameterDirection

private theorem localizedStateParameterDirection_flow_jet
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (v : StateDirections S × ℝ) (hvq : v.2 = 0)
    (m n b : ℕ) (θ r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m))
    (η : HeightPair S) (c : ℝ)
    (hheight : ∀ t ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S η (t, ψ) = heightPairField S v.1.val.1 (t, ψ) + c)
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y)))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (vs : Fin n → (StateDirections S × ℝ)) :
    J.D (n + 1) z (Fin.snoc vs v) = J.D (n + 1) z (Fin.snoc vs
      (localizedStateParameterDirection (hS.2.1 (3 / 4 : ℝ)) m η
        ((S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m 0))) := by
  let c₀ : ℝ := (S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m 0
  let w : StateDirections S × ℝ :=
    localizedStateParameterDirection (hS.2.1 (3 / 4 : ℝ)) m η c₀
  have hwq : w.2 = 0 :=
    localizedStateParameterDirection_scalar (hS.2.1 (3 / 4 : ℝ)) m η c₀
  have hκ : (S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m 0 =
      (S.circle (3 / 4 : ℝ)).decode w.1.val.2.2.1 m 0 := by
    have heq := localizedStateParameterDirection_control
      (hS.2.1 (3 / 4 : ℝ)) m η c₀ m 0
    change c₀ = (S.circle (3 / 4 : ℝ)).decode
      (localizedStateParameterDirection (hS.2.1 (3 / 4 : ℝ)) m η c₀).1.val.2.2.1 m 0
    simpa only [if_pos rfl, ite_true] using heq.symm
  have hh : ∀ t ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S v.1.val.1 (t, ψ) = heightPairField S w.1.val.1 (t, ψ) + -c := by
    intro t ht ψ
    have hw : w.1.val.1 = η :=
      localizedStateParameterDirection_height (hS.2.1 (3 / 4 : ℝ)) m η c₀
    have heq : heightPairField S w.1.val.1 (t, ψ) = heightPairField S η (t, ψ) :=
      congrArg (fun ξ : HeightPair S => heightPairField S ξ (t, ψ)) hw
    linarith only [heq, hheight t ht ψ]
  exact hN.ordinaryFlowFamily_state_jet_locality hS hT hz v w hvq hwq
    m b θ hr hκ (-c) hh J n vs

private theorem exists_localized_state_directions_from_height
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (v : StateDirections S × ℝ) (hvq : v.2 = 0)
    (η : ℕ → HeightPair S)
    (hlocal : ∀ m, ∃ c : ℝ, ∀ t ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
      heightPairField S (η m) (t, θ) = heightPairField S v.1.val.1 (t, θ) + c)
    (henergy : ∀ s m, heightPairGrading S s (η m) ≤
      Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) s
        ((S.height (3 / 4 : ℝ)).decode v.1.val.1.1) m).toReal) :
    ∃ w : ℕ → (StateDirections S × ℝ),
      (∀ m, (w m).2 = 0) ∧
      (∀ m n b θ r (hr : r ∈ Icc (C.left m) (C.right m))
        (J : SmoothDirections (sectorNeighborhood S base ε ε)
          (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y))),
        ∀ z ∈ sectorNeighborhood S base ε ε, ∀ vs : Fin n → (StateDirections S × ℝ),
          J.D (n + 1) z (Fin.snoc vs v) = J.D (n + 1) z (Fin.snoc vs (w m))) ∧
      (∀ m s d,
        T.M (T.sample m) ^ d * pairGrading (sectorGrading S) realGrading s (w m) ≤
          T.M (T.sample m) ^ d *
            Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) s
              ((S.height (3 / 4 : ℝ)).decode v.1.val.1.1) m).toReal +
          (circleSingletonGradingConstant s * (2 * circleSobolevConstant)) *
            Real.sqrt (circleComponentEnergy T (3 / 4 : ℝ) (s + d + 1)
              ((S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1) m).toReal) := by
  let w : ℕ → (StateDirections S × ℝ) := fun m =>
    localizedStateParameterDirection (hS.2.1 (3 / 4 : ℝ)) m (η m)
      ((S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1 m 0)
  have hwq (m : ℕ) : (w m).2 = 0 :=
    localizedStateParameterDirection_scalar (hS.2.1 (3 / 4 : ℝ)) m (η m) _
  refine ⟨w, hwq, ?_, ?_⟩
  · intro m n b θ r hr J z hz vs
    let c : ℝ := (hlocal m).choose
    have hc : ∀ t ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
        heightPairField S (η m) (t, θ) = heightPairField S v.1.val.1 (t, θ) + c :=
      (hlocal m).choose_spec
    exact localizedStateParameterDirection_flow_jet hN hS hT v hvq
      m n b θ r hr (η m) c hc J z hz vs
  · intro m s d
    have hs := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
    have hM : 1 ≤ T.M (T.sample m) := (hT.2.1 _ hs).2.2.2
    have hH : 0 ≤ T.H (T.sample m) := (hT.2.1 _ hs).2.1.le
    exact (localizedStateParameterDirection_weighted_grading_le (hS.2.1 (3 / 4 : ℝ))
      v.1.val.2.2.1 m s d (η m) hM hH).trans
      (add_le_add (mul_le_mul_of_nonneg_left (henergy s m)
        (pow_nonneg (zero_le_one.trans hM) d)) (le_refl _))

theorem N01Properties.exists_localized_state_directions
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (v : StateDirections S × ℝ) (hvq : v.2 = 0) :
    ∃ w : ℕ → (StateDirections S × ℝ),
      (∀ m, (w m).2 = 0) ∧
      (∀ m n b θ r (hr : r ∈ Icc (C.left m) (C.right m))
        (J : SmoothDirections (sectorNeighborhood S base ε ε)
          (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y))),
        ∀ z ∈ sectorNeighborhood S base ε ε, ∀ vs : Fin n → (StateDirections S × ℝ),
          J.D (n + 1) z (Fin.snoc vs v) = J.D (n + 1) z (Fin.snoc vs (w m))) ∧
      (∀ m s d,
        T.M (T.sample m) ^ d * pairGrading (sectorGrading S) realGrading s (w m) ≤
          T.M (T.sample m) ^ d *
            Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) s
              ((S.height (3 / 4 : ℝ)).decode v.1.val.1.1) m).toReal +
          (circleSingletonGradingConstant s * (2 * circleSobolevConstant)) *
            Real.sqrt (circleComponentEnergy T (3 / 4 : ℝ) (s + d + 1)
              ((S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1) m).toReal) := by
  let data := N01Properties.exists_height_pair_plateau_directions
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT (show HeightPair S from v.1.val.1)
  exact exists_localized_state_directions_from_height hN hS hT v hvq data.choose
    data.choose_spec.2.2.1 (fun s m => (data.choose_spec.2.2.2 s).2 m)

end ContinuousFlexibility.Statements
