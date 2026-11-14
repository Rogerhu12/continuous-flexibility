module

public import ContinuousFlexibility.Analysis.N01PlateauEnergyEnvelope

/-!
# A fixed two-order bound for the actual localization envelope

The constant is chosen before the input height. All local grading
energies are summed, including the full expanded supports. The total is
bounded by the square of one actual input grading two orders higher.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.physicalPlateauEnergy_tsum_le_grading_sq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε γ : ℝ} {H : SobolevModelData}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (hH : IsSobolevModel D T γ H) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : H.Space,
      (∑' m : ℕ, physicalPlateauEnergy D T C γ s (H.decode u) m) ≤
        ENNReal.ofReal (K * H.grading (s + 2) u ^ 2) := by
  classical
  have ha (a : Fin (s + 1)) := hN.controlPlateau_cutoff_jet_energy_tsum_le hT a.val
  choose Ka hKa hjet using ha
  let K₀ : ℝ := ∑ a : Fin (s + 1), Ka a * ((a.val + 1 : ℕ) : ℝ)
  have hK₀ : 0 ≤ K₀ :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hKa a) (Nat.cast_nonneg _))
  have hKa₀ (a : Fin (s + 1)) : Ka a * ((a.val + 1 : ℕ) : ℝ) ≤ K₀ :=
    Finset.single_le_sum (f := fun i : Fin (s + 1) => Ka i * ((i.val + 1 : ℕ) : ℝ))
      (fun i _ => mul_nonneg (hKa i) (Nat.cast_nonneg _))
      (Finset.mem_univ a)
  let N : ℕ := ∑ i : Fin (s + 1), Fintype.card (JetIndex i.val)
  refine ⟨(N : ℝ) * K₀, mul_nonneg (Nat.cast_nonneg _) hK₀, fun u => ?_⟩
  let Q : ℝ := H.grading (s + 2) u ^ 2
  have hQ : 0 ≤ Q := sq_nonneg _
  have hu := hH.2.2.2.1 u
  have hj (a b c : ℕ) (horder : a + b + c ≤ s) :
      (∑' m : ℕ, eLpNorm (weightedPhysicalJet T γ a b c
        (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u)))
          2 materialCylinderMeasure ^ 2) ≤ ENNReal.ofReal (K₀ * Q) := by
    let ai : Fin (s + 1) := ⟨a, by omega⟩
    have hin (i : Fin (a + 1)) :
        eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + 2) (H.decode u))
          2 materialCylinderMeasure ^ 2 ≤ ENNReal.ofReal Q :=
      sobolevModel_weightedJet_energy_le_grading_sq hH u (by omega)
    have hsum : (∑ i : Fin (a + 1),
        eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + 2) (H.decode u))
          2 materialCylinderMeasure ^ 2) ≤ ENNReal.ofReal (((a + 1 : ℕ) : ℝ) * Q) := by
      calc
        _ ≤ ∑ _i : Fin (a + 1), ENNReal.ofReal Q := Finset.sum_le_sum (fun i _ => hin i)
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    calc
      _ ≤ ENNReal.ofReal (Ka ai) * ∑ i : Fin (a + 1),
          eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + 2) (H.decode u))
            2 materialCylinderMeasure ^ 2 := hjet ai γ (H.decode u) hu b c
      _ ≤ ENNReal.ofReal (Ka ai) * ENNReal.ofReal (((a + 1 : ℕ) : ℝ) * Q) :=
        mul_le_mul_right hsum _
      _ = ENNReal.ofReal ((Ka ai * ((a + 1 : ℕ) : ℝ)) * Q) := by
        rw [← ENNReal.ofReal_mul (hKa ai)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hKa₀ ai) hQ)
  have hlevel (i : Fin (s + 1)) :
      (∑' m : ℕ, physicalLevelEnergy T γ i.val
        (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u))) ≤
        (Fintype.card (JetIndex i.val) : ℝ≥0∞) * ENNReal.ofReal (K₀ * Q) := by
    have heq : (∑' m : ℕ, physicalLevelEnergy T γ i.val
        (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u))) =
        ∑ j : JetIndex i.val, ∑' m : ℕ,
          eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
            (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u)))
            2 materialCylinderMeasure ^ 2 := by
      simpa only [physicalLevelEnergy, tsum_fintype] using ENNReal.tsum_comm
        (f := fun m (j : JetIndex i.val) =>
          eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
            (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u)))
            2 materialCylinderMeasure ^ 2)
    rw [heq]
    calc
      _ ≤ ∑ _j : JetIndex i.val, ENNReal.ofReal (K₀ * Q) := by
        apply Finset.sum_le_sum
        intro j hj'
        exact hj _ _ _ (by have hi := j.property; have his := i.isLt; omega)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcomm : (∑' m : ℕ, physicalPlateauEnergy D T C γ s (H.decode u) m) =
      ∑ i : Fin (s + 1), ∑' m : ℕ, physicalLevelEnergy T γ i.val
        (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u)) := by
    simpa only [physicalPlateauEnergy, tsum_fintype] using ENNReal.tsum_comm
      (f := fun m (i : Fin (s + 1)) => physicalLevelEnergy T γ i.val
        (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u)))
  calc
    _ ≤ ∑ i : Fin (s + 1),
        (Fintype.card (JetIndex i.val) : ℝ≥0∞) * ENNReal.ofReal (K₀ * Q) := by
      rw [hcomm]
      exact Finset.sum_le_sum (fun i _ => hlevel i)
    _ = (N : ℝ≥0∞) * ENNReal.ofReal (K₀ * Q) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum]
    _ = ENNReal.ofReal ((N : ℝ) * (K₀ * Q)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = _ := by dsimp only [Q]; congr 1; ring

end ContinuousFlexibility.Statements
