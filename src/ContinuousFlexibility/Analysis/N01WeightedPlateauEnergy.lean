import ContinuousFlexibility.Analysis.N01PlateauEnergy
import ContinuousFlexibility.Analysis.N01PlateauMaterialPowers
import ContinuousFlexibility.Analysis.WeightedCutoffJetEnergy

/-!
# Summing local height jets with the actual return-label material weight

The material sample power enters the local integrand before summation.
Three orders transfer that power to the expanded support, one order
controls cutoff derivatives, and one controls support overlap. The total
additional order is five, independently of the output material power.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.controlPlateau_weighted_jet_energy_tsum_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (a d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : ℝ) (f : PolarPoint → ℝ), HeightMember D T γ f →
      ∀ b c : ℕ,
      (∑' m : ℕ, ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2) *
        eLpNorm (weightedPhysicalJet T γ a b c
          (radialPlateauLocalization D T (C.left m) (C.right m) f))
          2 materialCylinderMeasure ^ 2) ≤
        ENNReal.ofReal K * ∑ i : Fin (a + 1),
          eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + d + 5) f)
            2 materialCylinderMeasure ^ 2 := by
  classical
  obtain ⟨Kc, hKc, hcoeff⟩ := hN.controlPlateau_cutoff_coeff_bound hT a
  obtain ⟨Kw, hKw, hweight⟩ := hN.controlPlateau_material_pow_bound hS hT d
  obtain ⟨Ko, hKo, hover⟩ := hN.controlPlateau_material_overlap_bound hT
  let P : ℝ := ((a + 1 : ℕ) : ℝ) * (Kw * Kc) ^ 2
  have hP : 0 ≤ P := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  refine ⟨P * Ko, mul_nonneg hP hKo.le, fun γ f hf b c => ?_⟩
  let A : ℕ → Set PolarPoint := controlPlateauMaterialStrip D T C
  let g (m : ℕ) (i : Fin (a + 1)) : ℝ≥0∞ :=
    eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + (d + 4)) f)
      2 (materialCylinderMeasure.restrict (A m)) ^ 2
  have hA (m : ℕ) : MeasurableSet (A m) := controlPlateauMaterialStrip_measurable hT C m
  have hc : controlGeometryConditions D S C := hN.2.2.2.1
  have hsample (m : ℕ) : 0 ≤ T.M (T.sample m) :=
    zero_le_one.trans (hT.2.1 _
      (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m)).2.2.2
  have hm (m : ℕ) :
      ENNReal.ofReal ((T.M (T.sample m) ^ d) ^ 2) *
        eLpNorm (weightedPhysicalJet T γ a b c
          (radialPlateauLocalization D T (C.left m) (C.right m) f))
          2 materialCylinderMeasure ^ 2 ≤ ENNReal.ofReal P * ∑ i : Fin (a + 1), g m i := by
    have hχ := materialPlateauCutoff_contDiff hT (C.left m) (C.right m)
      (endpointPlateauWidth D (C.left m) (C.right m))
    have hcut := radialPlateauLocalization_member hT hf (hc.1 m).1 (hc.1 m).2.2
    apply weightedPhysicalJet_weighted_cutoff_energy_le hT hχ hf hcut
      (mul_nonneg hKw.le hKc) (hA m) a b c (d + 4) (T.M (T.sample m) ^ d)
    · intro p hp i
      have hMp : 0 ≤ T.M (T.radius p.1) :=
        zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.2.2
      rw [abs_mul, abs_of_nonneg (pow_nonneg (hsample m) d)]
      have hh := mul_le_mul (hweight m (T.radius p.1) hp) (hcoeff m i p.1)
        (abs_nonneg _) (mul_nonneg hKw.le (pow_nonneg hMp (d + 3)))
      exact hh.trans_eq (by rw [show d + 4 = (d + 3) + 1 by omega, pow_succ]; ring)
    · intro p hp i hi
      exact materialPlateauCutoff_iteratedDeriv_zero_off_support hT
        (endpointPlateauWidth_pos (hc.1 m).1 (hc.1 m).2.2) hp i
  have hi (i : Fin (a + 1)) :
      (∑' m : ℕ, g m i) ≤ ENNReal.ofReal Ko *
        eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + d + 5) f)
          2 materialCylinderMeasure ^ 2 := by
    simpa only [g, Nat.add_assoc, Nat.reduceAdd] using
      weightedPhysicalJet_restricted_energy_tsum_le hT hf hKo.le hA
        (fun p => (hover p).1) (fun p => (hover p).2) (a - i.val) b (c + (d + 4))
  have hcomm : (∑' m : ℕ, ∑ i : Fin (a + 1), g m i) =
      ∑ i : Fin (a + 1), ∑' m : ℕ, g m i := by
    simpa only [tsum_fintype] using ENNReal.tsum_comm (f := g)
  calc
    _ ≤ ∑' m : ℕ, ENNReal.ofReal P * ∑ i : Fin (a + 1), g m i :=
      ENNReal.tsum_le_tsum hm
    _ = ENNReal.ofReal P * ∑ i : Fin (a + 1), ∑' m : ℕ, g m i := by
      rw [ENNReal.tsum_mul_left, hcomm]
    _ ≤ ENNReal.ofReal P * ∑ i : Fin (a + 1), ENNReal.ofReal Ko *
        eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + d + 5) f)
          2 materialCylinderMeasure ^ 2 :=
      mul_le_mul_right (Finset.sum_le_sum (fun i _ => hi i)) _
    _ = _ := by rw [← Finset.mul_sum, ENNReal.ofReal_mul hP, mul_assoc]

end ContinuousFlexibility.Statements
