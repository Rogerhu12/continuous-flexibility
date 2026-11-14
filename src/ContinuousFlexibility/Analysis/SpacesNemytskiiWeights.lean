module

public import ContinuousFlexibility.Analysis.MaterialOrdinaryJets
public import ContinuousFlexibility.Analysis.SpacesNemytskiiScalar

/-!
# Radial coefficients in the composition jet formula

Differentiating a physical power of `H` preserves that power. Products and
derivatives preserve the corresponding class of radial coefficients, so
the number of height factors, rather than the spatial derivative order,
determines the power left in a normalized composition jet.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

def SpacesRadialMultiplier (T : MaterialData) (α : ℝ) (A : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ A ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
    |iteratedDeriv n A x| ≤ C * T.H (T.radius x) ^ α

theorem SpacesRadialMultiplier.contDiff {T : MaterialData} {α : ℝ} {A : ℝ → ℝ}
    (hA : SpacesRadialMultiplier T α A) : ContDiff ℝ ∞ A := hA.1

theorem SpacesRadialMultiplier.bound {T : MaterialData} {α : ℝ} {A : ℝ → ℝ}
    (hA : SpacesRadialMultiplier T α A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |A x| ≤ C * T.H (T.radius x) ^ α := by
  simpa only [iteratedDeriv_zero] using hA.2 0

theorem SpacesRadialMultiplier.deriv {T : MaterialData} {α : ℝ} {A : ℝ → ℝ}
    (hA : SpacesRadialMultiplier T α A) : SpacesRadialMultiplier T α (deriv A) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hA.1).2, fun n => ?_⟩
  simpa only [iteratedDeriv_succ'] using hA.2 (n + 1)

theorem spacesRadialMultiplier_materialH {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (α : ℝ) :
    SpacesRadialMultiplier T α (fun x => T.H (T.radius x) ^ α) := by
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    (hT.1 T.H (by simp)).comp_contDiff hT.2.2.2.2.2.2.1
      (fun x => (hT.2.2.2.2.2.2.2.1 x).1)
  refine ⟨hH.rpow_const_of_ne (fun x => (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.1.ne'), ?_⟩
  exact iteratedDeriv_materialH_rpow_bound hT α

theorem SpacesRadialMultiplier.mul {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {α β : ℝ} {A B : ℝ → ℝ}
    (hA : SpacesRadialMultiplier T α A) (hB : SpacesRadialMultiplier T β B) :
    SpacesRadialMultiplier T (α + β) (fun x => A x * B x) := by
  choose CA hCA hAbound using hA.2
  choose CB hCB hBbound using hB.2
  refine ⟨hA.1.mul hB.1, fun n => ?_⟩
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CA i * CB (n - i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA i)) (hCB (n - i)))
  refine ⟨C, hC, fun x => ?_⟩
  have hH : 0 < T.H (T.radius x) := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.1
  rw [iteratedDeriv_fun_mul (hA.1.contDiffAt.of_le (by simp)) (hB.1.contDiffAt.of_le (by simp))]
  calc
    |∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDeriv i A x * iteratedDeriv (n - i) B x| ≤
        ∑ i ∈ Finset.range (n + 1),
          |(n.choose i : ℝ) * iteratedDeriv i A x * iteratedDeriv (n - i) B x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * CA i * CB (n - i)) * T.H (T.radius x) ^ (α + β) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        (n.choose i : ℝ) * |iteratedDeriv i A x| * |iteratedDeriv (n - i) B x| ≤
            (n.choose i : ℝ) * (CA i * T.H (T.radius x) ^ α) *
              (CB (n - i) * T.H (T.radius x) ^ β) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hAbound i x) (Nat.cast_nonneg _))
            (hBbound (n - i) x) (abs_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hCA i) (Real.rpow_pos_of_pos hH α).le))
        _ = _ := by rw [Real.rpow_add hH]; ring
    _ = C * T.H (T.radius x) ^ (α + β) := (Finset.sum_mul _ _ _).symm

theorem SpacesRadialMultiplier.bounded_of_nonneg {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {α : ℝ} (hα : 0 ≤ α) {A : ℝ → ℝ}
    (hA : SpacesRadialMultiplier T α A) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |A x| ≤ C := by
  obtain ⟨B, hB, hb⟩ := hA.bound
  rcases eq_or_lt_of_le hα with he | hp
  · refine ⟨B, hB, fun x => ?_⟩
    simpa only [← he, Real.rpow_zero, mul_one] using hb x
  · obtain ⟨L, hL, hbound, _, _⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.2.1 0 α hp
    refine ⟨B * L, mul_nonneg hB hL.le, fun x => ?_⟩
    apply (hb x).trans
    apply mul_le_mul_of_nonneg_left _ hB
    simpa only [Real.rpow_zero, mul_one] using hbound _ (hT.2.2.2.2.2.2.2.1 x).1

end ContinuousFlexibility.Statements
