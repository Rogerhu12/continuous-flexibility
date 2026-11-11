import ContinuousFlexibility.Analysis.MaterialCutoffJetEnergy

/-!
# Sample-weighted local physical jet energies

A scalar component weight is kept inside the actual localized jet.
The coefficient estimate may absorb any prescribed material power on
the support. The resulting L2 bound uses that precise additional input
material order, without differentiating a material multiplier.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

theorem weightedPhysicalJet_add_material_order
    (T : MaterialData) (γ : ℝ) (a b c d : ℕ)
    (f : PolarPoint → ℝ) (p : PolarPoint) :
    weightedPhysicalJet T γ a b (c + d) f p =
      T.M (T.radius p.1) ^ d * weightedPhysicalJet T γ a b c f p := by
  simp only [weightedPhysicalJet, pow_add]
  ring

theorem weightedPhysicalJet_weighted_cutoff_sq_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {χ : ℝ → ℝ} {f : PolarPoint → ℝ} {K : ℝ}
    (hT : IsMaterialData D T) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (hK : 0 ≤ K)
    (a b c d : ℕ) (w : ℝ) (p : PolarPoint)
    (hcoeff : ∀ i : Fin (a + 1),
      |w * ((a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1)| ≤
        K * T.M (T.radius p.1) ^ d) :
    |w * weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f) p| ^ 2 ≤
      ((a + 1 : ℕ) : ℝ) * K ^ 2 *
        ∑ i : Fin (a + 1), |weightedPhysicalJet T γ (a - i.val) b (c + d) f p| ^ 2 := by
  classical
  have hM : 0 ≤ T.M (T.radius p.1) :=
    zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.2.2
  have hterm (i : Fin (a + 1)) :
      |(w * ((a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1)) *
        weightedPhysicalJet T γ (a - i.val) b c f p| ≤
      K * |weightedPhysicalJet T γ (a - i.val) b (c + d) f p| := by
    rw [weightedPhysicalJet_add_material_order]
    calc
      _ = |w * ((a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1)| *
          |weightedPhysicalJet T γ (a - i.val) b c f p| := abs_mul _ _
      _ ≤ (K * T.M (T.radius p.1) ^ d) *
          |weightedPhysicalJet T γ (a - i.val) b c f p| :=
        mul_le_mul_of_nonneg_right (hcoeff i) (abs_nonneg _)
      _ = K * |T.M (T.radius p.1) ^ d *
          weightedPhysicalJet T γ (a - i.val) b c f p| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hM d)]
        ring
  have hexpand : w * weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f) p =
      ∑ i : Fin (a + 1),
        (w * ((a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1)) *
          weightedPhysicalJet T γ (a - i.val) b c f p := by
    rw [weightedPhysicalJet_cutoff hT hχ hf, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have habs : |w * weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f) p| ≤
      K * ∑ i : Fin (a + 1), |weightedPhysicalJet T γ (a - i.val) b (c + d) f p| := by
    rw [hexpand]
    calc
      _ ≤ ∑ i : Fin (a + 1),
          |(w * ((a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1)) *
            weightedPhysicalJet T γ (a - i.val) b c f p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (a + 1),
          K * |weightedPhysicalJet T γ (a - i.val) b (c + d) f p| :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcs : (∑ i : Fin (a + 1),
      |weightedPhysicalJet T γ (a - i.val) b (c + d) f p|) ^ 2 ≤
      ((a + 1 : ℕ) : ℝ) * ∑ i : Fin (a + 1),
        |weightedPhysicalJet T γ (a - i.val) b (c + d) f p| ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin (a + 1) => |weightedPhysicalJet T γ (a - i.val) b (c + d) f p|))
  calc
    _ ≤ (K * ∑ i : Fin (a + 1),
        |weightedPhysicalJet T γ (a - i.val) b (c + d) f p|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = K ^ 2 * (∑ i : Fin (a + 1),
        |weightedPhysicalJet T γ (a - i.val) b (c + d) f p|) ^ 2 := mul_pow _ _ _
    _ ≤ K ^ 2 * (((a + 1 : ℕ) : ℝ) * ∑ i : Fin (a + 1),
        |weightedPhysicalJet T γ (a - i.val) b (c + d) f p| ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg K)
    _ = _ := by ring

theorem eLpNorm_const_mul_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (w : ℝ) :
    eLpNorm (fun p => w * f p) 2 μ ^ 2 = ENNReal.ofReal (w ^ 2) * eLpNorm f 2 μ ^ 2 := by
  have heq : (fun p => w * f p) = w • f := rfl
  rw [heq, eLpNorm_const_smul, mul_pow, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg w), sq_abs]

theorem weightedPhysicalJet_weighted_cutoff_energy_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {χ : ℝ → ℝ} {f : PolarPoint → ℝ} {K : ℝ} {A : Set PolarPoint}
    (hT : IsMaterialData D T) (hχ : ContDiff ℝ ∞ χ)
    (hf : HeightMember D T γ f)
    (hcut : HeightMember D T γ (materialCutoffHeight T χ f))
    (hK : 0 ≤ K) (hA : MeasurableSet A) (a b c d : ℕ) (w : ℝ)
    (hcoeff : ∀ p ∈ A, ∀ i : Fin (a + 1),
      |w * ((a.choose i.val : ℝ) * iteratedDeriv i.val χ p.1)| ≤
        K * T.M (T.radius p.1) ^ d)
    (hzero : ∀ p, p ∉ A → ∀ i : ℕ, i ≤ a → iteratedDeriv i χ p.1 = 0) :
    ENNReal.ofReal (w ^ 2) *
      eLpNorm (weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f))
        2 materialCylinderMeasure ^ 2 ≤
      ENNReal.ofReal (((a + 1 : ℕ) : ℝ) * K ^ 2) *
        ∑ i : Fin (a + 1), eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + d) f)
          2 (materialCylinderMeasure.restrict A) ^ 2 := by
  rw [← eLpNorm_const_mul_sq]
  apply eLpNorm_sq_le_finset_restricted_energy Finset.univ hA
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg K))
    (aestronglyMeasurable_const.mul (hcut.2.2.2.2 a b c).aestronglyMeasurable)
    (fun i _ => (hf.2.2.2.2 (a - i.val) b (c + d)).aestronglyMeasurable)
  · intro p hp
    have hjet : weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f) p = 0 := by
      rw [weightedPhysicalJet_cutoff hT hχ hf.1]
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero p hp i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), mul_zero, zero_mul]
    simp only [Pi.mul_apply, hjet, mul_zero]
  · intro p hp
    exact weightedPhysicalJet_weighted_cutoff_sq_le hT hχ hf.1 hK a b c d w p (hcoeff p hp)

end ContinuousFlexibility.Statements
