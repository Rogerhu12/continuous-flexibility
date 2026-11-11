import ContinuousFlexibility.Analysis.FiniteRestrictedEnergy
import ContinuousFlexibility.Analysis.MaterialHeightCutoff

/-!
# Actual squared jet estimates for radial localization

The exact radial Leibniz formula and a finite Cauchy--Schwarz estimate
bound a localized jet by restricted input energies. One material order
absorbs the scalar cutoff derivative bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem weightedPhysicalJet_cutoff_sq_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {χ : ℝ → ℝ} {f : PolarPoint → ℝ} {K : ℝ}
    (hT : IsMaterialData D T) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (hK : 0 ≤ K)
    (a b c : ℕ) (p : PolarPoint)
    (hcoeff : ∀ i : Fin (a + 1),
      |(a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1| ≤ K * T.M (T.radius p.1)) :
    |weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f) p| ^ 2 ≤
      ((a + 1 : ℕ) : ℝ) * K ^ 2 *
        ∑ i : Fin (a + 1), |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p| ^ 2 := by
  classical
  have hM : 0 ≤ T.M (T.radius p.1) :=
    zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.2.2
  have hterm (i : Fin (a + 1)) :
      |(a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1 *
        weightedPhysicalJet T γ (a - i.val) b c f p| ≤
      K * |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p| := by
    rw [abs_mul, weightedPhysicalJet_succ_material_order, abs_mul, abs_of_nonneg hM]
    exact (mul_le_mul_of_nonneg_right (hcoeff i) (abs_nonneg _)).trans_eq (by ring)
  have habs : |weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f) p| ≤
      K * ∑ i : Fin (a + 1), |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p| := by
    rw [weightedPhysicalJet_cutoff hT hχ hf, ← Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑ i : Fin (a + 1),
          |(a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1 *
            weightedPhysicalJet T γ (a - i.val) b c f p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (a + 1),
          K * |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p| :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcs : (∑ i : Fin (a + 1),
      |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p|) ^ 2 ≤
      ((a + 1 : ℕ) : ℝ) * ∑ i : Fin (a + 1),
        |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p| ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin (a + 1) => |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p|))
  calc
    _ ≤ (K * ∑ i : Fin (a + 1),
        |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = K ^ 2 * (∑ i : Fin (a + 1),
        |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p|) ^ 2 := mul_pow _ _ _
    _ ≤ K ^ 2 * (((a + 1 : ℕ) : ℝ) * ∑ i : Fin (a + 1),
        |weightedPhysicalJet T γ (a - i.val) b (c + 1) f p| ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg K)
    _ = _ := by ring

theorem weightedPhysicalJet_cutoff_energy_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {χ : ℝ → ℝ} {f : PolarPoint → ℝ} {K : ℝ} {A : Set PolarPoint}
    (hT : IsMaterialData D T) (hχ : ContDiff ℝ ∞ χ)
    (hf : HeightMember D T γ f)
    (hcut : HeightMember D T γ (materialCutoffHeight T χ f))
    (hK : 0 ≤ K) (hA : MeasurableSet A) (a b c : ℕ)
    (hcoeff : ∀ p, ∀ i : Fin (a + 1),
      |(a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1| ≤ K * T.M (T.radius p.1))
    (hzero : ∀ p, p ∉ A → ∀ i : ℕ, i ≤ a → iteratedDeriv i χ p.1 = 0) :
    eLpNorm (weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f))
      2 materialCylinderMeasure ^ 2 ≤
      ENNReal.ofReal (((a + 1 : ℕ) : ℝ) * K ^ 2) *
        ∑ i : Fin (a + 1), eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + 1) f)
          2 (materialCylinderMeasure.restrict A) ^ 2 := by
  apply eLpNorm_sq_le_finset_restricted_energy Finset.univ hA
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg K))
    (hcut.2.2.2.2 a b c).aestronglyMeasurable
    (fun i _ => (hf.2.2.2.2 (a - i.val) b (c + 1)).aestronglyMeasurable)
  · intro p hp
    rw [weightedPhysicalJet_cutoff hT hχ hf.1]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero p hp i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), mul_zero, zero_mul]
  · intro p hp
    exact weightedPhysicalJet_cutoff_sq_le hT hχ hf.1 hK a b c p (hcoeff p)

end ContinuousFlexibility.Statements
