import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Summing actual height energies over negative components

The radial components in N01 are pairwise disjoint.  Their preimages in
the actual material coordinate are also disjoint.  Consequently the sum
of all restricted physical jet energies is bounded by the original
global physical energy.  The conclusion concerns the actual decoder
and the full infinite sum over components.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

def componentMaterialStrip (T : MaterialData) (l r : ℝ) : Set PolarPoint :=
  {p | T.radius p.1 ∈ Ioo l r}

def physicalComponentEnergy (T : MaterialData) (γ : ℝ) (s : ℕ)
    (f : PolarPoint → ℝ) (l r : ℝ) : ℝ≥0∞ :=
  ∑ j : JetIndex s,
    eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
      2 (materialCylinderMeasure.restrict (componentMaterialStrip T l r)) ^ 2

def physicalComponentNorm (T : MaterialData) (γ : ℝ) (s : ℕ)
    (f : PolarPoint → ℝ) (l r : ℝ) : ℝ :=
  Real.sqrt (physicalComponentEnergy T γ s f l r).toReal

private theorem eLpNorm_two_sq_eq_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf)

private theorem disjoint_restricted_L2_energy_sum_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A : ℕ → Set α} {f : α → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hdisjoint : Pairwise (fun m n => Disjoint (A m) (A n)))
    (hf : MemLp f 2 μ) :
    (∑' m, eLpNorm f 2 (μ.restrict (A m)) ^ 2) ≤ eLpNorm f 2 μ ^ 2 := by
  simp_rw [eLpNorm_two_sq_eq_lintegral (hf.restrict _).aestronglyMeasurable]
  rw [← lintegral_iUnion hA hdisjoint]
  rw [eLpNorm_two_sq_eq_lintegral hf.aestronglyMeasurable]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

theorem physicalEnergy_lt_top {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) (s : ℕ) :
    (∑ j : JetIndex s,
      eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
        2 materialCylinderMeasure ^ 2) < ⊤ := by
  apply ENNReal.sum_lt_top.mpr
  intro j hj
  rw [pow_two]
  exact ENNReal.mul_lt_top (hf.2.2.2.2 _ _ _) (hf.2.2.2.2 _ _ _)

theorem physicalComponentEnergy_lt_top {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f)
    (s : ℕ) (l r : ℝ) :
    physicalComponentEnergy T γ s f l r < ⊤ := by
  apply ENNReal.sum_lt_top.mpr
  intro j hj
  rw [pow_two]
  exact ENNReal.mul_lt_top ((hf.2.2.2.2 _ _ _).restrict _)
    ((hf.2.2.2.2 _ _ _).restrict _)

/-- Pairwise disjoint physical intervals give the same exact estimate
after the material-coordinate change. -/
theorem physicalComponentEnergy_tsum_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f)
    {l r : ℕ → ℝ}
    (hdisjoint : Pairwise (fun m n => Disjoint (Ioo (l m) (r m)) (Ioo (l n) (r n))))
    (s : ℕ) :
    (∑' m, physicalComponentEnergy T γ s f (l m) (r m)) ≤
      ∑ j : JetIndex s,
        eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
          2 materialCylinderMeasure ^ 2 := by
  obtain ⟨_, _, _, _, _, _, hradius, _⟩ := hT
  have hA (m : ℕ) : MeasurableSet (componentMaterialStrip T (l m) (r m)) :=
    (isOpen_Ioo.preimage (hradius.continuous.comp continuous_fst)).measurableSet
  have hd : Pairwise (fun m n =>
      Disjoint (componentMaterialStrip T (l m) (r m))
        (componentMaterialStrip T (l n) (r n))) := by
    intro m n hmn
    exact Set.disjoint_left.mpr fun p hp hq => Set.disjoint_left.mp (hdisjoint hmn) hp hq
  calc
    (∑' m, physicalComponentEnergy T γ s f (l m) (r m)) =
        ∑ j : JetIndex s, ∑' m,
          eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
            2 (materialCylinderMeasure.restrict (componentMaterialStrip T (l m) (r m))) ^ 2 := by
      simpa only [physicalComponentEnergy, tsum_fintype] using
        (ENNReal.tsum_comm (f := fun m (j : JetIndex s) =>
          eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
            2 (materialCylinderMeasure.restrict (componentMaterialStrip T (l m) (r m))) ^ 2))
    _ ≤ _ := Finset.sum_le_sum fun j _ =>
      disjoint_restricted_L2_energy_sum_le hA hd (hf.2.2.2.2 _ _ _)

theorem physicalComponentNorm_sq_tsum_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f)
    {l r : ℕ → ℝ}
    (hdisjoint : Pairwise (fun m n => Disjoint (Ioo (l m) (r m)) (Ioo (l n) (r n))))
    (s : ℕ) :
    (∑' m, physicalComponentNorm T γ s f (l m) (r m) ^ 2) ≤
      physicalNorm T γ s f ^ 2 := by
  have hsum := physicalComponentEnergy_tsum_le hT hf hdisjoint s
  have hterm (m : ℕ) :
      physicalComponentEnergy T γ s f (l m) (r m) ≠ ⊤ :=
    (physicalComponentEnergy_lt_top hf s (l m) (r m)).ne
  simp only [physicalComponentNorm, physicalNorm, Real.sq_sqrt ENNReal.toReal_nonneg]
  rw [← ENNReal.tsum_toReal_eq hterm]
  exact ENNReal.toReal_mono (physicalEnergy_lt_top hf s).ne hsum

/-- The concrete N01 negative components satisfy the infinite energy
bound without any additional localization or overlap hypothesis. -/
theorem N01Properties.minusComponentNorm_sq_tsum_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (γ : ℝ) (u : (S.height γ).Space) (s : ℕ) :
    (∑' m, physicalComponentNorm T γ s ((S.height γ).decode u) (C.left m) (C.right m) ^ 2) ≤
      physicalNorm T γ s ((S.height γ).decode u) ^ 2 := by
  have hc : controlGeometryConditions D S C := hN01.2.2.2.1
  exact physicalComponentNorm_sq_tsum_le hT ((hS.1 γ).2.2.2.1 u)
    (fun m n hmn => hc.2.2.1 m n hmn) s

theorem N01Properties.minusComponentEnergy_decode_tsum_lt_top
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (γ : ℝ) (u : (S.height γ).Space) (s : ℕ) :
    (∑' m, physicalComponentEnergy T γ s ((S.height γ).decode u)
      (C.left m) (C.right m)) < ⊤ := by
  have hc : controlGeometryConditions D S C := hN01.2.2.2.1
  have hu := (hS.1 γ).2.2.2.1 u
  exact (physicalComponentEnergy_tsum_le hT hu
    (fun m n hmn => hc.2.2.1 m n hmn) s).trans_lt (physicalEnergy_lt_top hu s)

end ContinuousFlexibility.Statements
