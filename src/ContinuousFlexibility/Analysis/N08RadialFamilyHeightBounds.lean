import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets
import ContinuousFlexibility.Analysis.N08MaterialWeightIntegrability
import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveBounds
import ContinuousFlexibility.Scalar.WeightedJetNorm

/-!
# Actual weighted height norms of radial families

All weighted jets are dominated by the same positive material-height power,
which is square integrable on the full cylinder. The finite physical jet
norm therefore has a uniform bound by the weak control norm at every order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ENNReal ContDiff

variable {D : ReferenceData} {T : MaterialData}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ → ℝ}

theorem n08RadialFamilyField_contDiffOn
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b)) (u : E) :
    ContDiffOn ℝ ∞ (n08RadialFamilyField F u) (annularOpen D) :=
  (hF u).comp contDiff_fst.contDiffOn (fun _ hp => hp.1)

theorem n08RadialFamilyField_weightedJet_L2_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * ‖u‖ * T.H r ^ (3 / 128 : ℝ) * T.M r) (a b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E,
      MemLp (weightedPhysicalJet T n08WeakControlWeight a b c (n08RadialFamilyField F u))
        2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T n08WeakControlWeight a b c (n08RadialFamilyField F u))
        2 materialCylinderMeasure).toReal ≤ K * ‖u‖ := by
  obtain ⟨K, hK, hKb⟩ := n08RadialFamilyField_weightedJet_bound hT hF hB a b c
  let W : PolarPoint → ℝ := fun p => T.H (T.radius p.1) ^ (n08WeakControlWeight / 2)
  have hW : MemLp W 2 materialCylinderMeasure :=
    n08_memLp_cylinder_materialH_rpow hT (half_pos n08WeakControlWeight_pos)
  refine ⟨K * (eLpNorm W 2 materialCylinderMeasure).toReal,
    mul_nonneg hK ENNReal.toReal_nonneg, fun u => ?_⟩
  have hm : AEStronglyMeasurable
      (weightedPhysicalJet T n08WeakControlWeight a b c (n08RadialFamilyField F u))
        materialCylinderMeasure :=
    (contDiff_weightedPhysicalJet hT (n08RadialFamilyField_contDiffOn hF u)
      a b c).continuous.aestronglyMeasurable
  have hae : ∀ᵐ p ∂materialCylinderMeasure,
      ‖weightedPhysicalJet T n08WeakControlWeight a b c (n08RadialFamilyField F u) p‖ ≤
        (K * ‖u‖) * ‖W p‖ := by
    apply Eventually.of_forall
    intro p
    have hp := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.1
    simpa only [Real.norm_eq_abs, W, abs_of_pos (Real.rpow_pos_of_pos hp _)] using hKb u p
  refine ⟨hW.of_le_mul hm hae, ?_⟩
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hae 2
  have hfinite : ENNReal.ofReal (K * ‖u‖) * eLpNorm W 2 materialCylinderMeasure ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.eLpNorm_lt_top).ne
  have hr := ENNReal.toReal_mono hfinite he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK (norm_nonneg _))] at hr
  exact hr.trans_eq (by ring)

theorem n08RadialFamilyField_heightMember
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * ‖u‖ * T.H r ^ (3 / 128 : ℝ) * T.M r)
    (hzero : ∀ u r, r ∉ Ioo D.a D.b → F u r = 0) (u : E) :
    HeightMember D T n08WeakControlWeight (n08RadialFamilyField F u) := by
  refine ⟨n08RadialFamilyField_contDiffOn hF u, fun _ _ => rfl, ?_,
    fun p hp => hzero u p.1 (fun hr => hp ⟨hr, mem_univ _⟩), ?_⟩
  · intro p
    change F u (p.1 + 0) = F u p.1
    rw [add_zero]
  · intro a b c
    obtain ⟨_, _, h⟩ := n08RadialFamilyField_weightedJet_L2_bound hT hF hB a b c
    exact (h u).1

/-- One weak Banach norm controls every actual weighted physical norm.
The constant may depend on the output order; the input order is always zero. -/
theorem n08RadialFamilyField_physicalNorm_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * ‖u‖ * T.H r ^ (3 / 128 : ℝ) * T.M r) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E,
      physicalNorm T n08WeakControlWeight s (n08RadialFamilyField F u) ≤ K * ‖u‖ := by
  classical
  choose B hBpos hBx using fun j : JetIndex s =>
    n08RadialFamilyField_weightedJet_L2_bound hT hF hB
      (j.val 0).val (j.val 1).val (j.val 2).val
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hBpos j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun i _ => hBpos i) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, fun u => ?_⟩
  have hmem (a b c : ℕ) (_ : a + b + c ≤ s) :
      MemLp (weightedPhysicalJet T n08WeakControlWeight a b c (n08RadialFamilyField F u))
        2 materialCylinderMeasure := by
    obtain ⟨_, _, h⟩ := n08RadialFamilyField_weightedJet_L2_bound hT hF hB a b c
    exact (h u).1
  have hbound (a b c : ℕ) (horder : a + b + c ≤ s) :
      (eLpNorm (weightedPhysicalJet T n08WeakControlWeight a b c (n08RadialFamilyField F u))
        2 materialCylinderMeasure).toReal ≤ K * ‖u‖ := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj : (eLpNorm (weightedPhysicalJet T n08WeakControlWeight a b c
        (n08RadialFamilyField F u)) 2 materialCylinderMeasure).toReal ≤ B j * ‖u‖ := by
      simpa [j] using (hBx j u).2
    exact hj.trans (mul_le_mul_of_nonneg_right (hBK j) (norm_nonneg _))
  exact (physicalNorm_le_of_weightedJet_bounds (mul_nonneg hK (norm_nonneg _))
    hmem hbound).trans_eq (by ring)

end ContinuousFlexibility.Statements
