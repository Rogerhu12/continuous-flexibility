import ContinuousFlexibility.Analysis.N06CubicMultiplierSymmetry

/-!
# Local angular jet bounds for the actual cubic multipliers

Only interior smoothness of the divided coefficients is used. Every
angular jet of the five actual multipliers uses coefficient jets of the
same angular order, together with the first spatial derivatives already
present in divergence. No extension across a degenerate endpoint is
required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem n06_angularJet_radial_three_at (a b c : ℝ → ℝ)
    (F G H : PolarPoint → ℝ) (p : PolarPoint)
    (hF : ContDiff ℝ ∞ (fun θ => F (p.1, θ)))
    (hG : ContDiff ℝ ∞ (fun θ => G (p.1, θ)))
    (hH : ContDiff ℝ ∞ (fun θ => H (p.1, θ))) (k : ℕ) :
    mixedDerivative 0 k (fun q => a q.1 * F q + b q.1 * G q + c q.1 * H q) p =
      a p.1 * mixedDerivative 0 k F p + b p.1 * mixedDerivative 0 k G p +
        c p.1 * mixedDerivative 0 k H p := by
  have h₁ : ContDiff ℝ ∞ (fun θ => a p.1 * F (p.1, θ)) := contDiff_const.mul hF
  have h₂ : ContDiff ℝ ∞ (fun θ => b p.1 * G (p.1, θ)) := contDiff_const.mul hG
  have h₃ : ContDiff ℝ ∞ (fun θ => c p.1 * H (p.1, θ)) := contDiff_const.mul hH
  simp only [mixedDerivative, iteratedDeriv_zero]
  rw [iteratedDeriv_fun_add ((h₁.add h₂).contDiffAt.of_le (by simp))
      (h₃.contDiffAt.of_le (by simp)),
    iteratedDeriv_fun_add (h₁.contDiffAt.of_le (by simp)) (h₂.contDiffAt.of_le (by simp))]
  simp only [iteratedDeriv_const_mul_field]

/-- The actual multiplier jets, expressed directly in local mixed jets
of the three divided principal coefficients. -/
theorem n06CubicGraphMultipliers_angularJet_componentsOn_strip
    {l r : ℝ} (d e : ℝ → ℝ) {A B C : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo l r ×ˢ (univ : Set ℝ)))
    (hB : ContDiffOn ℝ ∞ B (Ioo l r ×ˢ (univ : Set ℝ)))
    (hC : ContDiffOn ℝ ∞ C (Ioo l r ×ˢ (univ : Set ℝ)))
    (k : ℕ) (i : Fin 5) (p : PolarPoint) (hp : p.1 ∈ Ioo l r) :
    mixedDerivative 0 k (n06CubicGraphMultipliers d e A B C i) p =
      ![d p.1 * mixedDerivative 0 k A p,
        2 * Real.sqrt (d p.1) * mixedDerivative 0 k B p,
        mixedDerivative 0 k C p,
        d p.1 * (3 * e p.1 * mixedDerivative 0 k A p +
          d p.1 * mixedDerivative 1 k A p + d p.1 * mixedDerivative 0 (k + 1) B p),
        Real.sqrt (d p.1) * (3 * e p.1 * mixedDerivative 0 k B p +
          d p.1 * mixedDerivative 1 k B p + d p.1 * mixedDerivative 0 (k + 1) C p)] i := by
  have hU : IsOpen (Ioo l r ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hpU : p ∈ Ioo l r ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
  have hs {F : PolarPoint → ℝ} (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ))) :
      ContDiff ℝ ∞ (fun θ => F (p.1, θ)) :=
    hF.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun θ => ⟨hp, mem_univ θ⟩)
  have hsumA :
      mixedDerivative 0 k (fun q => 3 * e q.1 * A q + d q.1 * radialPartial A q +
        d q.1 * angularPartial B q) p =
      3 * e p.1 * mixedDerivative 0 k A p + d p.1 * mixedDerivative 1 k A p +
        d p.1 * mixedDerivative 0 (k + 1) B p := by
    rw [n06_angularJet_radial_three_at (fun x => 3 * e x) d d A
      (radialPartial A) (angularPartial B) p (hs hA)
      (hs (scalar_contDiffOn_radialPartial hU hA))
      (hs (scalar_contDiffOn_angularPartial hU hB)) k,
      mixedDerivative_radialPartial hU hA 0 k hpU,
      mixedDerivative_angularPartial hU hB 0 k hpU]
  have hsumB :
      mixedDerivative 0 k (fun q => 3 * e q.1 * B q + d q.1 * radialPartial B q +
        d q.1 * angularPartial C q) p =
      3 * e p.1 * mixedDerivative 0 k B p + d p.1 * mixedDerivative 1 k B p +
        d p.1 * mixedDerivative 0 (k + 1) C p := by
    rw [n06_angularJet_radial_three_at (fun x => 3 * e x) d d B
      (radialPartial B) (angularPartial C) p (hs hB)
      (hs (scalar_contDiffOn_radialPartial hU hB))
      (hs (scalar_contDiffOn_angularPartial hU hC)) k,
      mixedDerivative_radialPartial hU hB 0 k hpU,
      mixedDerivative_angularPartial hU hC 0 k hpU]
  fin_cases i
  · exact congrFun (n06_angularJet_radial_mul d A k) p
  · exact congrFun (n06_angularJet_radial_mul (fun x => 2 * Real.sqrt (d x)) B k) p
  · rfl
  · change mixedDerivative 0 k (fun q => d q.1 *
        (3 * e q.1 * A q + d q.1 * radialPartial A q + d q.1 * angularPartial B q)) p = _
    rw [n06_angularJet_radial_mul d _ k]
    change d p.1 * mixedDerivative 0 k
      (fun q => 3 * e q.1 * A q + d q.1 * radialPartial A q + d q.1 * angularPartial B q) p = _
    rw [hsumA]
    rfl
  · change mixedDerivative 0 k (fun q => Real.sqrt (d q.1) *
        (3 * e q.1 * B q + d q.1 * radialPartial B q + d q.1 * angularPartial C q)) p = _
    rw [n06_angularJet_radial_mul (fun x => Real.sqrt (d x)) _ k]
    change Real.sqrt (d p.1) * mixedDerivative 0 k
      (fun q => 3 * e q.1 * B q + d q.1 * radialPartial B q + d q.1 * angularPartial C q) p = _
    rw [hsumB]
    rfl

/-- Spatial coefficient jets through `b + 1` control the multiplier jets
through `b`, including both odd multipliers, by the explicit factor five. -/
theorem n06CubicGraphMultipliers_angularJet_abs_leOn_strip
    {l r : ℝ} (d e : ℝ → ℝ) {A B C : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo l r ×ˢ (univ : Set ℝ)))
    (hB : ContDiffOn ℝ ∞ B (Ioo l r ×ˢ (univ : Set ℝ)))
    (hC : ContDiffOn ℝ ∞ C (Ioo l r ×ˢ (univ : Set ℝ)))
    {b : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (p : PolarPoint) (hp : p.1 ∈ Ioo l r)
    (hd : 0 ≤ d p.1) (hd₁ : d p.1 ≤ 1) (he : |e p.1| ≤ 1)
    (hcoeff : ∀ a j : ℕ, a + j ≤ b + 1 →
      |mixedDerivative a j A p| ≤ δ ∧ |mixedDerivative a j B p| ≤ δ ∧
        |mixedDerivative a j C p| ≤ δ)
    (k : ℕ) (hk : k ≤ b) (i : Fin 5) :
    |mixedDerivative 0 k (n06CubicGraphMultipliers d e A B C i) p| ≤ 5 * δ := by
  have h₀ := hcoeff 0 k (by omega)
  have hr := hcoeff 1 k (by omega)
  have ht := hcoeff 0 (k + 1) (by omega)
  have hprod (w x M : ℝ) (hw : 0 ≤ w) (hw₁ : w ≤ 1) (hx : |x| ≤ M) :
      |w * x| ≤ M := by
    rw [abs_mul, abs_of_nonneg hw]
    simpa only [one_mul] using mul_le_mul hw₁ hx (abs_nonneg x) zero_le_one
  have hs : Real.sqrt (d p.1) ≤ 1 := Real.sqrt_le_one.mpr hd₁
  rw [n06CubicGraphMultipliers_angularJet_componentsOn_strip d e hA hB hC k i p hp]
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_zero', Matrix.cons_val_succ', id_eq]
  · exact (hprod _ _ _ hd hd₁ h₀.1).trans (by linarith only [hδ])
  · calc
      |2 * Real.sqrt (d p.1) * mixedDerivative 0 k B p| =
          2 * |Real.sqrt (d p.1) * mixedDerivative 0 k B p| := by
            rw [mul_assoc, abs_mul]
            norm_num
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left
        (hprod _ _ _ (Real.sqrt_nonneg _) hs h₀.2.1) (by norm_num)
      _ ≤ 5 * δ := by linarith only [hδ]
  · exact h₀.2.2.trans (by linarith only [hδ])
  · exact hprod _ _ _ hd hd₁ (n06_cubic_firstOrder_abs hd hd₁ he h₀.1 hr.1 ht.2.1)
  · exact hprod _ _ _ (Real.sqrt_nonneg _) hs
      (n06_cubic_firstOrder_abs hd hd₁ he h₀.2.1 hr.2.1 ht.2.2)

end ContinuousFlexibility.Analysis
