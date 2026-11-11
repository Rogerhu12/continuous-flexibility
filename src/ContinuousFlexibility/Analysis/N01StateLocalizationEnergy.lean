import ContinuousFlexibility.Analysis.N01LocalizedStateDirections
import ContinuousFlexibility.Analysis.N01WeightedPlateauEnvelope

/-!
# A summable energy for actual localized state directions

The envelope is the sum of the localized physical height energy and the
original circle-control component energy. It has a uniform bound in one
actual state seminorm at order s+d+5. The same localized directions work
for every s and d, and no base state is replaced by a large cutoff state.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01StateLocalizationEnergyStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

def stateLocalizationEnergy (D : ReferenceData) (T : MaterialData)
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (s d : ℕ) (v : StateDirections S × ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2) *
    physicalPlateauEnergy D T C (3 / 4 : ℝ) s
      ((S.height (3 / 4 : ℝ)).decode v.1.val.1.1) m +
  circleComponentEnergy T (3 / 4 : ℝ) (s + d + 1)
    ((S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1) m

private theorem stateLocalization_pairGrading_fst_le
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (n : ℕ) (v : E × F) :
    p n v.1 ≤ pairGrading p q n v := by
  rw [pairGrading_apply]
  exact le_add_of_nonneg_right (apply_nonneg (q n) v.2)

theorem sectorParameter_height_grading_le
    (S : PhysicalSpacesData) (n : ℕ) (v : StateDirections S × ℝ) :
    (S.height (3 / 4 : ℝ)).grading n v.1.val.1.1 ≤
      pairGrading (sectorGrading S) realGrading n v := by
  calc
    _ ≤ heightPairGrading S n v.1.val.1 := by
      change (S.height (3 / 4 : ℝ)).grading n v.1.val.1.1 ≤
        (S.height (3 / 4 : ℝ)).grading n v.1.val.1.1 + realGrading n v.1.val.1.2
      exact le_add_of_nonneg_right (apply_nonneg _ _)
    _ ≤ sectorGrading S n v.1 := by
      change heightPairGrading S n v.1.val.1 ≤
        heightPairGrading S n v.1.val.1 +
          (realGrading n v.1.val.2.1 +
            ((S.circle (3 / 4 : ℝ)).grading n v.1.val.2.2.1 +
              (S.circle (3 / 4 : ℝ)).grading n v.1.val.2.2.2))
      exact le_add_of_nonneg_right (add_nonneg (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
    _ ≤ _ := stateLocalization_pairGrading_fst_le (sectorGrading S) realGrading n v

theorem sectorParameter_control_grading_le
    (S : PhysicalSpacesData) (n : ℕ) (v : StateDirections S × ℝ) :
    (S.circle (3 / 4 : ℝ)).grading n v.1.val.2.2.1 ≤
      pairGrading (sectorGrading S) realGrading n v := by
  have hκ : 0 ≤ (S.circle (3 / 4 : ℝ)).grading n v.1.val.2.2.1 := apply_nonneg _ _
  have hh : 0 ≤ (S.circle (3 / 4 : ℝ)).grading n v.1.val.2.2.2 := apply_nonneg _ _
  have hν : 0 ≤ realGrading n v.1.val.2.1 := apply_nonneg _ _
  have hη : 0 ≤ heightPairGrading S n v.1.val.1 := apply_nonneg _ _
  have hq : 0 ≤ realGrading n v.2 := apply_nonneg _ _
  change (S.circle (3 / 4 : ℝ)).grading n v.1.val.2.2.1 ≤
    (heightPairGrading S n v.1.val.1 + (realGrading n v.1.val.2.1 +
      ((S.circle (3 / 4 : ℝ)).grading n v.1.val.2.2.1 +
        (S.circle (3 / 4 : ℝ)).grading n v.1.val.2.2.2))) + realGrading n v.2
  linarith only [hh, hν, hη, hq]

theorem circleComponentEnergy_tsum_eq_ofReal_norm_sq
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (s : ℕ) :
    (∑' m : ℕ, circleComponentEnergy T γ s u m) =
      ENNReal.ofReal (circleNorm T γ s u ^ 2) := by
  rw [circleNorm, Real.sq_sqrt ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (hu.2.2 s).ne]
  rfl

theorem circleModel_componentEnergy_tsum_le_grading_sq
    {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    (hH : IsCircleModel T γ H) (u : H.Space) (s : ℕ) :
    (∑' m : ℕ, circleComponentEnergy T γ s (H.decode u) m) ≤
      ENNReal.ofReal (H.grading s u ^ 2) := by
  rw [circleComponentEnergy_tsum_eq_ofReal_norm_sq (hH.2.2.2.1 u)]
  have hnorm : circleNorm T γ s (H.decode u) ≤ H.grading s u :=
    ((circleGrading_le_iff_circleNorm hH s u (apply_nonneg _ _)).mp
      (le_refl (H.grading s u))) s le_rfl
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2)

private theorem stateLocalizationEnergy_tsum_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hC : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (s d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hheight : ∀ u : (S.height (3 / 4 : ℝ)).Space,
      (∑' m : ℕ, ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2) *
        physicalPlateauEnergy D T C (3 / 4 : ℝ) s
          ((S.height (3 / 4 : ℝ)).decode u) m) ≤
        ENNReal.ofReal (K * (S.height (3 / 4 : ℝ)).grading (s + d + 5) u ^ 2))
    (v : StateDirections S × ℝ) :
    (∑' m : ℕ, stateLocalizationEnergy D T C s d v m) ≤
      ENNReal.ofReal ((K + 1) *
        (pairGrading (sectorGrading S) realGrading (s + d + 5) v) ^ 2) := by
  let P : ℝ := pairGrading (sectorGrading S) realGrading (s + d + 5) v
  have hPh : (S.height (3 / 4 : ℝ)).grading (s + d + 5) v.1.val.1.1 ≤ P :=
    sectorParameter_height_grading_le S (s + d + 5) v
  have hPc : (S.circle (3 / 4 : ℝ)).grading (s + d + 1) v.1.val.2.2.1 ≤ P :=
    (sectorParameter_control_grading_le S (s + d + 1) v).trans
      (sectorPairGrading_monotone S (by omega) v)
  have hh := (hheight v.1.val.1.1).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (apply_nonneg _ _) hPh 2) hK))
  have hc := (circleModel_componentEnergy_tsum_le_grading_sq
    hC v.1.val.2.2.1 (s + d + 1)).trans
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (apply_nonneg _ _) hPc 2))
  calc
    _ = (∑' m : ℕ, ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2) *
          physicalPlateauEnergy D T C (3 / 4 : ℝ) s
            ((S.height (3 / 4 : ℝ)).decode v.1.val.1.1) m) +
        ∑' m : ℕ, circleComponentEnergy T (3 / 4 : ℝ) (s + d + 1)
          ((S.circle (3 / 4 : ℝ)).decode v.1.val.2.2.1) m := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (K * P ^ 2) + ENNReal.ofReal (P ^ 2) := add_le_add hh hc
    _ = ENNReal.ofReal ((K + 1) * P ^ 2) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hK (sq_nonneg _)) (sq_nonneg _)]
      congr 1
      ring

theorem N01Properties.stateLocalizationEnergy_tsum_le_grading_sq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (s d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : StateDirections S × ℝ,
      (∑' m : ℕ, stateLocalizationEnergy D T C s d v m) ≤
        ENNReal.ofReal (K * (pairGrading (sectorGrading S) realGrading (s + d + 5) v) ^ 2) := by
  let data := N01Properties.physicalPlateauEnergy_weighted_tsum_le_grading_sq
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    (γ := (3 / 4 : ℝ)) (H := S.height (3 / 4 : ℝ))
    hN hS hT (hS.1 (3 / 4 : ℝ)) s d
  let K : ℝ := data.choose
  have hK : 0 ≤ K := data.choose_spec.1
  exact ⟨K + 1, add_nonneg hK zero_le_one,
    stateLocalizationEnergy_tsum_bound (hS.2.1 (3 / 4 : ℝ)) s d K hK data.choose_spec.2⟩

theorem N01Properties.stateLocalizationEnergy_tsum_lt_top
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (s d : ℕ) (v : StateDirections S × ℝ) :
    (∑' m : ℕ, stateLocalizationEnergy D T C s d v m) < ⊤ := by
  let data := hN.stateLocalizationEnergy_tsum_le_grading_sq hS hT s d
  exact (data.choose_spec.2 v).trans_lt ENNReal.ofReal_lt_top

private theorem sqrt_weighted_energy_bound
    {E F : ℝ≥0∞} {M c a : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hfinite : ENNReal.ofReal (M ^ 2) * E + F < ⊤)
    (ha : a ≤ M * Real.sqrt E.toReal + c * Real.sqrt F.toReal) :
    a ≤ (1 + c) * Real.sqrt (ENNReal.ofReal (M ^ 2) * E + F).toReal := by
  have hleft : ENNReal.ofReal (M ^ 2) * E ≤ ENNReal.ofReal (M ^ 2) * E + F :=
    le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ F from bot_le)
  have hh : M * Real.sqrt E.toReal ≤
      Real.sqrt (ENNReal.ofReal (M ^ 2) * E + F).toReal := by
    have hsqrt := Real.sqrt_le_sqrt (ENNReal.toReal_mono hfinite.ne hleft)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg M),
      Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM] using hsqrt
  have hright : F ≤ ENNReal.ofReal (M ^ 2) * E + F :=
    le_add_of_nonneg_left
      (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (M ^ 2) * E from bot_le)
  have hh' : Real.sqrt F.toReal ≤
      Real.sqrt (ENNReal.ofReal (M ^ 2) * E + F).toReal :=
    Real.sqrt_le_sqrt (ENNReal.toReal_mono hfinite.ne hright)
  exact ha.trans
    ((add_le_add hh (mul_le_mul_of_nonneg_left hh' hc)).trans_eq (by ring))

theorem N01Properties.exists_localized_state_energy_directions
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
          (1 + circleSingletonGradingConstant s * (2 * circleSobolevConstant)) *
            Real.sqrt (stateLocalizationEnergy D T C s d v m).toReal) := by
  let data := N01Properties.exists_localized_state_directions
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT v hvq
  let w : ℕ → (StateDirections S × ℝ) := data.choose
  refine ⟨w, data.choose_spec.1, data.choose_spec.2.1, fun m s d => ?_⟩
  have hfinite : stateLocalizationEnergy D T C s d v m < ⊤ :=
    (ENNReal.le_tsum (f := fun j : ℕ => stateLocalizationEnergy D T C s d v j) m).trans_lt
      (hN.stateLocalizationEnergy_tsum_lt_top hS hT s d v)
  have hD : IsAccumulatingProfile D := hN.1.1
  have hgeom : AccumulatingProfileBounds D hD.choose := hD.choose_spec
  have hM : 0 ≤ T.M (T.sample m) := zero_le_one.trans
    (hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)).2.2.2
  have hconstant : 0 ≤ circleSingletonGradingConstant s * (2 * circleSobolevConstant) :=
    mul_nonneg (circleSingletonGradingConstant_nonneg s)
      (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
  exact sqrt_weighted_energy_bound (pow_nonneg hM d) hconstant hfinite
    (data.choose_spec.2.2 m s d)

end ContinuousFlexibility.Statements
