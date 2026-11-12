import ContinuousFlexibility.Analysis.MaterialComponentEnergy
import ContinuousFlexibility.Analysis.N01cHeightSeminorms

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

theorem sobolevModel_physicalLevelEnergy_le_grading_sq
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (u : H.Space) (s : ℕ) :
    physicalLevelEnergy T γ s (H.decode u) ≤ ENNReal.ofReal (H.grading s u ^ 2) := by
  rw [physicalLevelEnergy_eq_ofReal_norm_sq (hH.2.2.2.1 u)]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (sobolevModel_physicalNorm_le_grading hH u (s := s) (t := s) le_rfl) 2)

theorem sobolevModel_weightedJet_energy_le_grading_sq
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (u : H.Space) {a b c s : ℕ}
    (horder : a + b + c ≤ s) :
    eLpNorm (weightedPhysicalJet T γ a b c (H.decode u)) 2 materialCylinderMeasure ^ 2 ≤
      ENNReal.ofReal (H.grading s u ^ 2) :=
  (weightedPhysicalJet_energy_le_level (H.decode u) horder).trans
    (sobolevModel_physicalLevelEnergy_le_grading_sq hH u s)

private theorem nonneg_le_sqrt_ennreal_of_sq_le
    {x : ℝ} {E : ℝ≥0∞} (hx : 0 ≤ x) (hE : E < ⊤)
    (hbound : ENNReal.ofReal (x ^ 2) ≤ E) : x ≤ Real.sqrt E.toReal := by
  have hsq : x ^ 2 ≤ E.toReal := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg x)] using
      ENNReal.toReal_mono hE.ne hbound
  have h := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq hx] using h

private theorem physicalNorm_nonneg_for_energy
    (T : MaterialData) (γ : ℝ) (i : ℕ) (f : PolarPoint → ℝ) :
    0 ≤ physicalNorm T γ i f := by
  unfold physicalNorm
  exact Real.sqrt_nonneg _

private theorem sqrt_ennreal_level_le_finite_sum
    (E : ℕ → ℝ≥0∞) (hE : ∀ j, E j < ⊤) {i s : ℕ} (hi : i ≤ s) :
    Real.sqrt (E i).toReal ≤ Real.sqrt (∑ j : Fin (s + 1), E j.val).toReal := by
  classical
  have hsum : (∑ j : Fin (s + 1), E j.val) < ⊤ :=
    ENNReal.sum_lt_top.mpr (fun j _ => hE j.val)
  have hle : E i ≤ ∑ j : Fin (s + 1), E j.val :=
    Finset.single_le_sum (f := fun j : Fin (s + 1) => E j.val)
      (fun _ _ => zero_le) (Finset.mem_univ ⟨i, Nat.lt_succ_of_le hi⟩)
  exact Real.sqrt_le_sqrt (ENNReal.toReal_mono hsum.ne hle)

private theorem physicalNorm_eq_sqrt_levelEnergy
    (T : MaterialData) (γ : ℝ) (i : ℕ) (f : PolarPoint → ℝ) :
    physicalNorm T γ i f = Real.sqrt (physicalLevelEnergy T γ i f).toReal := rfl

theorem physicalNorm_le_sqrt_levelEnergy_sum
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) {i s : ℕ} (hi : i ≤ s) :
    physicalNorm T γ i f ≤
      Real.sqrt (∑ j : Fin (s + 1), physicalLevelEnergy T γ j.val f).toReal := by
  exact (physicalNorm_eq_sqrt_levelEnergy T γ i f).trans_le
    (sqrt_ennreal_level_le_finite_sum (fun j => physicalLevelEnergy T γ j f)
      (fun j => physicalLevelEnergy_lt_top hf j) hi)

theorem sobolevModel_grading_le_iff_physicalNorm
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (u : H.Space) (s : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    H.grading s u ≤ C ↔ ∀ i ≤ s, physicalNorm T γ i (H.decode u) ≤ C := by
  obtain ⟨_, _, _, _, _, _, _, hnorm⟩ := hH
  simpa only [SobolevModelData.grading, hnorm] using
    gradedSeminorm_le_iff (fun i => H.level i) H.bond s u hC

theorem sobolevModel_grading_le_sqrt_energy_sum
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (u : H.Space) (s : ℕ) :
    H.grading s u ≤
      Real.sqrt (∑ i : Fin (s + 1), physicalLevelEnergy T γ i.val (H.decode u)).toReal := by
  apply (sobolevModel_grading_le_iff_physicalNorm hH u s (Real.sqrt_nonneg _)).mpr
  intro i hi
  exact physicalNorm_le_sqrt_levelEnergy_sum (hH.2.2.2.1 u) hi

end ContinuousFlexibility.Statements
