module

public import ContinuousFlexibility.Analysis.N01WeightedPlateauEnergy
public import ContinuousFlexibility.Analysis.N01PlateauEnergyEnvelope
public import ContinuousFlexibility.Analysis.FinitePhysicalEnergyBounds

/-!
# A summable physical localization envelope with sample material powers

The estimate is uniform in the decoded height. For local grading s and
sample material degree d, the actual input grading is s+d+5. The five
additional orders are independent of s and d.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.physicalPlateauEnergy_weighted_tsum_le_grading_sq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε γ : ℝ} {H : SobolevModelData}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hH : IsSobolevModel D T γ H) (s d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : H.Space,
      (∑' m : ℕ, ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2) *
        physicalPlateauEnergy D T C γ s (H.decode u) m) ≤
        ENNReal.ofReal (K * H.grading (s + d + 5) u ^ 2) := by
  classical
  have ha (a : Fin (s + 1)) :=
    hN.controlPlateau_weighted_jet_energy_tsum_le hS hT a.val d
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
  let Q : ℝ := H.grading (s + d + 5) u ^ 2
  have hQ : 0 ≤ Q := sq_nonneg _
  have hu := hH.2.2.2.1 u
  have hj (a b c : ℕ) (horder : a + b + c ≤ s) :
      (∑' m : ℕ, ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2) *
        eLpNorm (weightedPhysicalJet T γ a b c
          (radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u)))
          2 materialCylinderMeasure ^ 2) ≤ ENNReal.ofReal (K₀ * Q) := by
    let ai : Fin (s + 1) := ⟨a, by omega⟩
    have hin (i : Fin (a + 1)) :
        eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + d + 5) (H.decode u))
          2 materialCylinderMeasure ^ 2 ≤ ENNReal.ofReal Q :=
      sobolevModel_weightedJet_energy_le_grading_sq hH u (by omega)
    have hsum : (∑ i : Fin (a + 1),
        eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + d + 5) (H.decode u))
          2 materialCylinderMeasure ^ 2) ≤ ENNReal.ofReal (((a + 1 : ℕ) : ℝ) * Q) := by
      calc
        _ ≤ ∑ _i : Fin (a + 1), ENNReal.ofReal Q := Finset.sum_le_sum (fun i _ => hin i)
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    calc
      _ ≤ ENNReal.ofReal (Ka ai) * ∑ i : Fin (a + 1),
          eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + d + 5) (H.decode u))
            2 materialCylinderMeasure ^ 2 := hjet ai γ (H.decode u) hu b c
      _ ≤ ENNReal.ofReal (Ka ai) * ENNReal.ofReal (((a + 1 : ℕ) : ℝ) * Q) :=
        mul_le_mul_right hsum _
      _ = ENNReal.ofReal ((Ka ai * ((a + 1 : ℕ) : ℝ)) * Q) := by
        rw [← ENNReal.ofReal_mul (hKa ai)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hKa₀ ai) hQ)
  have hsum := physicalLevelEnergy_cumulative_weighted_tsum_le
    (fun m => ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2))
    (fun m => radialPlateauLocalization D T (C.left m) (C.right m) (H.decode u))
    s (ENNReal.ofReal (K₀ * Q)) hj
  calc
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (K₀ * Q) := hsum
    _ = ENNReal.ofReal ((N : ℝ) * (K₀ * Q)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = _ := by dsimp only [Q]; congr 1; ring

theorem N01Properties.physicalPlateauEnergy_weighted_tsum_lt_top
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε γ : ℝ} {H : SobolevModelData}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hH : IsSobolevModel D T γ H) (u : H.Space) (s d : ℕ) :
    (∑' m : ℕ, ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2) *
      physicalPlateauEnergy D T C γ s (H.decode u) m) < ⊤ := by
  obtain ⟨K, _, hK⟩ :=
    hN.physicalPlateauEnergy_weighted_tsum_le_grading_sq hS hT hH s d
  exact (hK u).trans_lt ENNReal.ofReal_lt_top

end ContinuousFlexibility.Statements
