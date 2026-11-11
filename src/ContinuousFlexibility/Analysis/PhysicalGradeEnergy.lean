import ContinuousFlexibility.Analysis.MaterialComponentEnergy

/-!
# Exact physical jet energy and the supplied projective grading

The finite jet sum is the square of the actual level norm. Individual
jets are controlled by the grading at their total order, and the sum of
the level energies up to an order controls that entire grading.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

def physicalLevelEnergy (T : MaterialData) (γ : ℝ) (s : ℕ)
    (f : PolarPoint → ℝ) : ℝ≥0∞ :=
  ∑ j : JetIndex s,
    eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
      2 materialCylinderMeasure ^ 2

theorem physicalLevelEnergy_lt_top {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) (s : ℕ) :
    physicalLevelEnergy T γ s f < ⊤ := physicalEnergy_lt_top hf s

theorem physicalLevelEnergy_eq_ofReal_norm_sq {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) (s : ℕ) :
    physicalLevelEnergy T γ s f = ENNReal.ofReal (physicalNorm T γ s f ^ 2) := by
  rw [physicalNorm, Real.sq_sqrt ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (physicalEnergy_lt_top hf s).ne]
  rfl

theorem weightedPhysicalJet_energy_le_level {T : MaterialData} {γ : ℝ}
    (f : PolarPoint → ℝ) {a b c s : ℕ} (horder : a + b + c ≤ s) :
    eLpNorm (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure ^ 2 ≤
      physicalLevelEnergy T γ s f := by
  classical
  let j : JetIndex s := ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using horder⟩
  have h := Finset.single_le_sum
    (f := fun k : JetIndex s =>
      eLpNorm (weightedPhysicalJet T γ (k.val 0).val (k.val 1).val (k.val 2).val f)
        2 materialCylinderMeasure ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ j)
  simpa only [j, physicalLevelEnergy, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem sobolevModel_physicalNorm_le_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (u : H.Space) (s : ℕ) :
    physicalNorm T γ s (H.decode u) ≤ H.grading s u := by
  rw [← hH.2.2.2.2.2.2.2 u s]
  exact norm_coordinate_le_graded _ _ le_rfl u

theorem sobolevModel_physicalLevelEnergy_le_grading_sq
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (u : H.Space) (s : ℕ) :
    physicalLevelEnergy T γ s (H.decode u) ≤ ENNReal.ofReal (H.grading s u ^ 2) := by
  rw [physicalLevelEnergy_eq_ofReal_norm_sq (hH.2.2.2.1 u)]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) (sobolevModel_physicalNorm_le_grading hH u s) 2)

theorem sobolevModel_weightedJet_energy_le_grading_sq
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (u : H.Space) {a b c s : ℕ}
    (horder : a + b + c ≤ s) :
    eLpNorm (weightedPhysicalJet T γ a b c (H.decode u)) 2 materialCylinderMeasure ^ 2 ≤
      ENNReal.ofReal (H.grading s u ^ 2) :=
  (weightedPhysicalJet_energy_le_level (H.decode u) horder).trans
    (sobolevModel_physicalLevelEnergy_le_grading_sq hH u s)

theorem sobolevModel_grading_le_sqrt_energy_sum
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (u : H.Space) (s : ℕ) :
    H.grading s u ≤
      Real.sqrt (∑ i : Fin (s + 1), physicalLevelEnergy T γ i.val (H.decode u)).toReal := by
  classical
  obtain ⟨i, hi, hgrade⟩ := gradedSeminorm_exists_norm _ _ s u
  change gradedSeminorm _ _ s u ≤ _
  rw [hgrade, hH.2.2.2.2.2.2.2 u i]
  let k : Fin (s + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  have hsum : (∑ i : Fin (s + 1), physicalLevelEnergy T γ i.val (H.decode u)) < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro j hj
    exact physicalLevelEnergy_lt_top (hH.2.2.2.1 u) j.val
  have hle : physicalLevelEnergy T γ i (H.decode u) ≤
      ∑ j : Fin (s + 1), physicalLevelEnergy T γ j.val (H.decode u) :=
    Finset.single_le_sum
      (f := fun j : Fin (s + 1) => physicalLevelEnergy T γ j.val (H.decode u))
      (fun _ _ => by positivity) (Finset.mem_univ k)
  exact Real.sqrt_le_sqrt (ENNReal.toReal_mono hsum.ne hle)

end ContinuousFlexibility.Statements
