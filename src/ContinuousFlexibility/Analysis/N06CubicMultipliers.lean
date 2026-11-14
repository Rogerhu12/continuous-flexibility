module

public import ContinuousFlexibility.Analysis.N06CylinderGraphJets

/-!
# The actual five multipliers of a cubic divergence perturbation

The genuine cubic differential expression is a sum of five products with
the weighted graph fields. Pure angular jets commute with this factorization,
including its radial square-root weights.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def n06CubicGraphMultipliers (d e : ℝ → ℝ) (A B C : PolarPoint → ℝ) :
    Fin 5 → PolarPoint → ℝ :=
  ![fun p => d p.1 * A p,
    fun p => 2 * Real.sqrt (d p.1) * B p,
    C,
    fun p => d p.1 * (3 * e p.1 * A p + d p.1 * radialPartial A p +
      d p.1 * angularPartial B p),
    fun p => Real.sqrt (d p.1) * (3 * e p.1 * B p + d p.1 * radialPartial B p +
      d p.1 * angularPartial C p)]

theorem n06CubicGraphMultipliers_decomposition
    (d e : ℝ → ℝ) (A B C U : PolarPoint → ℝ) (p : PolarPoint) (hd : 0 ≤ d p.1) :
    n06CubicExpression (d p.1) (e p.1) (A p) (B p) (C p)
      (radialPartial A p) (angularPartial B p) (radialPartial B p) (angularPartial C p)
      (radialPartial (radialPartial U) p) (angularPartial (radialPartial U) p)
      (angularPartial (angularPartial U) p) (radialPartial U p) (angularPartial U p) =
        ∑ i, n06CubicGraphMultipliers d e A B C i p *
          n06CubicGraphFields (fun q => d q.1) U i p := by
  simp only [n06CubicGraphMultipliers, n06CubicGraphFields, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  unfold n06CubicExpression
  ring_nf
  simp only [Real.sq_sqrt hd]
  <;> ring

theorem n06CubicGraphMultipliers_continuous
    {d e : ℝ → ℝ} (hd : Continuous d) (he : Continuous e)
    {A B C : PolarPoint → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C) (i : Fin 5) :
    Continuous (n06CubicGraphMultipliers d e A B C i) := by
  have hd' : Continuous (fun p : PolarPoint => d p.1) := hd.comp continuous_fst
  have he' : Continuous (fun p : PolarPoint => e p.1) := he.comp continuous_fst
  have hAr := (contDiff_cylinder_radialPartial hA).continuous
  have hBt := (contDiff_cylinder_angularPartial hB).continuous
  have hBr := (contDiff_cylinder_radialPartial hB).continuous
  have hCt := (contDiff_cylinder_angularPartial hC).continuous
  fin_cases i <;> simp only [n06CubicGraphMultipliers, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', id_eq]
  · exact hd'.mul hA.continuous
  · exact (continuous_const.mul hd'.sqrt).mul hB.continuous
  · exact hC.continuous
  · exact hd'.mul ((((continuous_const.mul he').mul hA.continuous).add
      (hd'.mul hAr)).add (hd'.mul hBt))
  · exact hd'.sqrt.mul ((((continuous_const.mul he').mul hB.continuous).add
      (hd'.mul hBr)).add (hd'.mul hCt))

theorem n06CubicGraphMultipliers_slice_smooth
    (d e : ℝ → ℝ) {A B C : PolarPoint → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C) (i : Fin 5) (r : ℝ) :
    ContDiff ℝ ∞ (fun θ => n06CubicGraphMultipliers d e A B C i (r, θ)) := by
  have hs {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) :
      ContDiff ℝ ∞ (fun θ => F (r, θ)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  fin_cases i <;> simp only [n06CubicGraphMultipliers, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', id_eq]
  · exact contDiff_const.mul (hs hA)
  · exact contDiff_const.mul (hs hB)
  · exact hs hC
  · exact contDiff_const.mul (((contDiff_const.mul (hs hA)).add
      (contDiff_const.mul (hs (contDiff_cylinder_radialPartial hA)))).add
        (contDiff_const.mul (hs (contDiff_cylinder_angularPartial hB))))
  · exact contDiff_const.mul (((contDiff_const.mul (hs hB)).add
      (contDiff_const.mul (hs (contDiff_cylinder_radialPartial hB)))).add
        (contDiff_const.mul (hs (contDiff_cylinder_angularPartial hC))))

theorem n06CubicGraphFields_slice_smooth (d : ℝ → ℝ)
    {U : PolarPoint → ℝ} (hU : ContDiff ℝ ∞ U) (i : Fin 5) (r : ℝ) :
    ContDiff ℝ ∞ (fun θ => n06CubicGraphFields (fun p => d p.1) U i (r, θ)) := by
  have hs {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) :
      ContDiff ℝ ∞ (fun θ => F (r, θ)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hr := contDiff_cylinder_radialPartial hU
  have ht := contDiff_cylinder_angularPartial hU
  fin_cases i <;> simp only [n06CubicGraphFields, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', id_eq]
  · exact contDiff_const.mul (hs (contDiff_cylinder_radialPartial hr))
  · exact contDiff_const.mul (hs (contDiff_cylinder_angularPartial hr))
  · exact contDiff_const.mul (hs (contDiff_cylinder_angularPartial ht))
  · exact contDiff_const.mul (hs hr)
  · exact contDiff_const.mul (hs ht)

private theorem n06_angularJet_radial_three (a b c : ℝ → ℝ)
    (F G H : PolarPoint → ℝ)
    (hF : ∀ r, ContDiff ℝ ∞ (fun θ => F (r, θ)))
    (hG : ∀ r, ContDiff ℝ ∞ (fun θ => G (r, θ)))
    (hH : ∀ r, ContDiff ℝ ∞ (fun θ => H (r, θ))) (k : ℕ) :
    mixedDerivative 0 k (fun p => a p.1 * F p + b p.1 * G p + c p.1 * H p) =
      fun p => a p.1 * mixedDerivative 0 k F p + b p.1 * mixedDerivative 0 k G p +
        c p.1 * mixedDerivative 0 k H p := by
  funext p
  have h₁ : ContDiff ℝ ∞ (fun θ => a p.1 * F (p.1, θ)) := contDiff_const.mul (hF p.1)
  have h₂ : ContDiff ℝ ∞ (fun θ => b p.1 * G (p.1, θ)) := contDiff_const.mul (hG p.1)
  have h₃ : ContDiff ℝ ∞ (fun θ => c p.1 * H (p.1, θ)) := contDiff_const.mul (hH p.1)
  have h₁₂ : ContDiff ℝ ∞ (fun θ => a p.1 * F (p.1, θ) + b p.1 * G (p.1, θ)) :=
    h₁.add h₂
  simp only [mixedDerivative, iteratedDeriv_zero]
  rw [iteratedDeriv_fun_add (h₁₂.contDiffAt.of_le (by simp))
      (h₃.contDiffAt.of_le (by simp)),
    iteratedDeriv_fun_add (h₁.contDiffAt.of_le (by simp)) (h₂.contDiffAt.of_le (by simp))]
  simp only [iteratedDeriv_const_mul_field]

/-- The multiplier jets involve the coefficient jets of the same angular
order and only the first spatial derivatives already present in divergence. -/
theorem n06CubicGraphMultipliers_angularJet (d e : ℝ → ℝ)
    {A B C : PolarPoint → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C) (k : ℕ) (i : Fin 5) :
    mixedDerivative 0 k (n06CubicGraphMultipliers d e A B C i) =
      n06CubicGraphMultipliers d e
        (mixedDerivative 0 k A) (mixedDerivative 0 k B) (mixedDerivative 0 k C) i := by
  have hs {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (r : ℝ) :
      ContDiff ℝ ∞ (fun θ => F (r, θ)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  fin_cases i
  · exact n06_angularJet_radial_mul d A k
  · exact n06_angularJet_radial_mul (fun y => 2 * Real.sqrt (d y)) B k
  · rfl
  · change mixedDerivative 0 k (fun p => d p.1 *
        (3 * e p.1 * A p + d p.1 * radialPartial A p + d p.1 * angularPartial B p)) = _
    rw [n06_angularJet_radial_mul d _ k,
      n06_angularJet_radial_three (fun y => 3 * e y) d d A (radialPartial A)
        (angularPartial B) (hs hA) (hs (contDiff_cylinder_radialPartial hA))
        (hs (contDiff_cylinder_angularPartial hB)) k]
    simp only [n06CubicGraphMultipliers, Matrix.cons_val_succ', Matrix.cons_val_zero',
      n06_radialPartial_angularJet hA k, n06_angularPartial_angularJet hB k]
  · change mixedDerivative 0 k (fun p => Real.sqrt (d p.1) *
        (3 * e p.1 * B p + d p.1 * radialPartial B p + d p.1 * angularPartial C p)) = _
    rw [n06_angularJet_radial_mul (fun y => Real.sqrt (d y)) _ k,
      n06_angularJet_radial_three (fun y => 3 * e y) d d B (radialPartial B)
        (angularPartial C) (hs hB) (hs (contDiff_cylinder_radialPartial hB))
        (hs (contDiff_cylinder_angularPartial hC)) k]
    simp only [n06CubicGraphMultipliers, Matrix.cons_val_succ', Matrix.cons_val_zero',
      n06_radialPartial_angularJet hB k, n06_angularPartial_angularJet hC k]

/-- The cubic graph multipliers are at most five times the coefficient
jet bound, uniformly up to either degenerate endpoint. -/
theorem n06CubicGraphMultipliers_abs_le
    (d e : ℝ → ℝ) (A B C : PolarPoint → ℝ) (p : PolarPoint) {δ : ℝ}
    (hd : 0 ≤ d p.1) (hd₁ : d p.1 ≤ 1) (he : |e p.1| ≤ 1) (hδ : 0 ≤ δ)
    (hA : |A p| ≤ δ) (hB : |B p| ≤ δ) (hC : |C p| ≤ δ)
    (hAr : |radialPartial A p| ≤ δ) (hBt : |angularPartial B p| ≤ δ)
    (hBr : |radialPartial B p| ≤ δ) (hCt : |angularPartial C p| ≤ δ) (i : Fin 5) :
    |n06CubicGraphMultipliers d e A B C i p| ≤ 5 * δ := by
  have hprod (w x M : ℝ) (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hx : |x| ≤ M) :
      |w * x| ≤ M := by
    rw [abs_mul, abs_of_nonneg hw]
    simpa only [one_mul] using mul_le_mul hw₁ hx (abs_nonneg x) zero_le_one
  have hs : Real.sqrt (d p.1) ≤ 1 := Real.sqrt_le_one.mpr hd₁
  fin_cases i
  · exact (hprod _ _ _ hd hd₁ hA).trans (by linarith only [hδ])
  · change |2 * Real.sqrt (d p.1) * B p| ≤ 5 * δ
    calc
      _ = 2 * |Real.sqrt (d p.1) * B p| := by rw [mul_assoc, abs_mul]; norm_num
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left
        (hprod _ _ _ (Real.sqrt_nonneg _) hs hB) (by norm_num)
      _ ≤ 5 * δ := by linarith only [hδ]
  · exact hC.trans (by linarith only [hδ])
  · exact hprod _ _ _ hd hd₁ (n06_cubic_firstOrder_abs hd hd₁ he hA hAr hBt)
  · exact hprod _ _ _ (Real.sqrt_nonneg _) hs
      (n06_cubic_firstOrder_abs hd hd₁ he hB hBr hCt)

end ContinuousFlexibility.Analysis
