import ContinuousFlexibility.Analysis.CoupledRadialFamilyMaterialJets
import ContinuousFlexibility.Analysis.CoupledMaterialWeightIntegrability
import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveBounds
import ContinuousFlexibility.Scalar.WeightedJetNorm

/-!
# Actual weighted height norms of radial families

All weighted jets are dominated by the same positive material-height power,
which is square integrable on the full cylinder. Monotonicity of the source
majorants bounds each finite physical norm at the same source order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ENNReal ContDiff

variable {D : ReferenceData} {T : MaterialData}
  {E : Type*} {F : E → ℝ → ℝ} {P : ℕ → E → ℝ}

theorem coupledRadialFamilyField_contDiffOn
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b)) (u : E) :
    ContDiffOn ℝ ∞ (coupledRadialFamilyField F u) (annularOpen D) :=
  (hF u).comp contDiff_fst.contDiffOn (fun _ hp => hp.1)

theorem coupledRadialFamilyField_weightedJet_L2_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hP : ∀ n u, 0 ≤ P n u) (hmono : Monotone P)
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * P s u * T.H r ^ (3 / 128 : ℝ) * T.M r) (a b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E,
      MemLp (weightedPhysicalJet T coupledWeakProfileWeight a b c (coupledRadialFamilyField F u))
        2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T coupledWeakProfileWeight a b c (coupledRadialFamilyField F u))
        2 materialCylinderMeasure).toReal ≤ K * P a u := by
  obtain ⟨K, hK, hKb⟩ := coupledRadialFamilyField_weightedJet_bound hT hF hP hmono hB a b c
  let W : PolarPoint → ℝ := fun p => T.H (T.radius p.1) ^ (coupledWeakProfileWeight / 2)
  have hW : MemLp W 2 materialCylinderMeasure :=
    coupled_memLp_cylinder_materialH_rpow hT (half_pos coupledWeakProfileWeight_pos)
  refine ⟨K * (eLpNorm W 2 materialCylinderMeasure).toReal,
    mul_nonneg hK ENNReal.toReal_nonneg, fun u => ?_⟩
  have hm : AEStronglyMeasurable
      (weightedPhysicalJet T coupledWeakProfileWeight a b c (coupledRadialFamilyField F u))
        materialCylinderMeasure :=
    (contDiff_weightedPhysicalJet hT (coupledRadialFamilyField_contDiffOn hF u)
      a b c).continuous.aestronglyMeasurable
  have hae : ∀ᵐ p ∂materialCylinderMeasure,
      ‖weightedPhysicalJet T coupledWeakProfileWeight a b c (coupledRadialFamilyField F u) p‖ ≤
        (K * P a u) * ‖W p‖ := by
    apply Eventually.of_forall
    intro p
    have hp := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.1
    simpa only [Real.norm_eq_abs, W, abs_of_pos (Real.rpow_pos_of_pos hp _)] using hKb u p
  refine ⟨hW.of_le_mul hm hae, ?_⟩
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hae 2
  have hfinite : ENNReal.ofReal (K * P a u) * eLpNorm W 2 materialCylinderMeasure ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.eLpNorm_lt_top).ne
  have hr := ENNReal.toReal_mono hfinite he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK (hP a u))] at hr
  exact hr.trans_eq (by ring)

theorem coupledRadialFamilyField_heightMember
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hP : ∀ n u, 0 ≤ P n u) (hmono : Monotone P)
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * P s u * T.H r ^ (3 / 128 : ℝ) * T.M r)
    (hzero : ∀ u r, r ∉ Ioo D.a D.b → F u r = 0) (u : E) :
    HeightMember D T coupledWeakProfileWeight (coupledRadialFamilyField F u) := by
  refine ⟨coupledRadialFamilyField_contDiffOn hF u, fun _ _ => rfl, ?_,
    fun p hp => hzero u p.1 (fun hr => hp ⟨hr, mem_univ _⟩), ?_⟩
  · intro p
    change F u (p.1 + 0) = F u p.1
    rw [add_zero]
  · intro a b c
    obtain ⟨_, _, h⟩ := coupledRadialFamilyField_weightedJet_L2_bound hT hF hP hmono hB a b c
    exact (h u).1

/-- No derivative loss is introduced by the passage from ordinary
positive-weight estimates to the physical height norm. -/
theorem coupledRadialFamilyField_physicalNorm_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hP : ∀ n u, 0 ≤ P n u) (hmono : Monotone P)
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * P s u * T.H r ^ (3 / 128 : ℝ) * T.M r) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E,
      physicalNorm T coupledWeakProfileWeight s (coupledRadialFamilyField F u) ≤ K * P s u := by
  classical
  choose B hBpos hBx using fun j : JetIndex s =>
    coupledRadialFamilyField_weightedJet_L2_bound hT hF hP hmono hB
      (j.val 0).val (j.val 1).val (j.val 2).val
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hBpos j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun i _ => hBpos i) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, fun u => ?_⟩
  have hmem (a b c : ℕ) (_ : a + b + c ≤ s) :
      MemLp (weightedPhysicalJet T coupledWeakProfileWeight a b c (coupledRadialFamilyField F u))
        2 materialCylinderMeasure := by
    obtain ⟨_, _, h⟩ := coupledRadialFamilyField_weightedJet_L2_bound hT hF hP hmono hB a b c
    exact (h u).1
  have hbound (a b c : ℕ) (horder : a + b + c ≤ s) :
      (eLpNorm (weightedPhysicalJet T coupledWeakProfileWeight a b c (coupledRadialFamilyField F u))
        2 materialCylinderMeasure).toReal ≤ K * P s u := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj : (eLpNorm (weightedPhysicalJet T coupledWeakProfileWeight a b c
        (coupledRadialFamilyField F u)) 2 materialCylinderMeasure).toReal ≤ B j * P a u := by
      simpa [j] using (hBx j u).2
    exact hj.trans (mul_le_mul (hBK j) (hmono (by omega : a ≤ s) u)
      (hP a u) hK)
  exact (physicalNorm_le_of_weightedJet_bounds (mul_nonneg hK (hP s u))
    hmem hbound).trans_eq (by ring)

end ContinuousFlexibility.Statements
