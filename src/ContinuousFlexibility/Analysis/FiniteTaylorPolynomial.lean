import ContinuousFlexibility.Analysis.IteratedFDerivSymmetry
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Finite Taylor polynomials of smooth real functions

The finite Taylor polynomial is the sum of the diagonal evaluations of
the jets at its center, divided by their factorials. Its derivatives at
the center agree with the given smooth function through the chosen order.
The top derivative is constant on the whole space and all higher
derivatives vanish. The construction needs neither analyticity of the
original function nor completeness of its target.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Equiv Set
open scoped ContDiff ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The full Taylor polynomial of degree at most `s`, centered at `q`. -/
def finiteTaylorPolynomial (s : ℕ) (f : E → F) (q : E) : E → F :=
  fun y => ∑ k ∈ Finset.range (s + 1),
    (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f q (fun _ => y - q)

/-- The finite coefficient series used by `finiteTaylorPolynomial`. -/
def finiteTaylorSeries (s : ℕ) (f : E → F) (q : E) : FormalMultilinearSeries ℝ E F :=
  fun k => if k ≤ s then (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f q else 0

/-- A finite Taylor polynomial has its specified finite power series on the
whole space, whether or not the original function is differentiable. -/
theorem finiteTaylorPolynomial_hasFiniteFPowerSeriesOnBall
    (s : ℕ) (f : E → F) (q : E) :
    HasFiniteFPowerSeriesOnBall (finiteTaylorPolynomial s f q)
      (finiteTaylorSeries s f q) q (s + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro k hk
    simp only [finiteTaylorSeries, ite_eq_right (show ¬k ≤ s by omega)]
  · exact ENNReal.zero_lt_top
  · intro y _
    simp only [finiteTaylorPolynomial, add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro k hk
    have hks : k ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    simp only [finiteTaylorSeries, ite_eq_left hks, ContinuousMultilinearMap.smul_apply]

/-- A finite Taylor polynomial is smooth of every order, including analytic
order. This assertion does not assume smoothness of the original function. -/
theorem contDiff_finiteTaylorPolynomial (s : ℕ) (f : E → F) (q : E) {n : ℕ∞ω} :
    ContDiff ℝ n (finiteTaylorPolynomial s f q) := by
  apply ContDiff.sum
  intro k _
  exact ContDiff.const_smul _ ((iteratedFDeriv ℝ k f q).contDiff.comp
    (contDiff_pi.mpr fun _ => contDiff_id.sub contDiff_const))

private theorem analyticOn_finiteTaylorPolynomial (s : ℕ) (f : E → F) (q : E) :
    AnalyticOn ℝ (finiteTaylorPolynomial s f q) univ :=
  (contDiff_finiteTaylorPolynomial s f q (n := ω)).contDiffOn.analyticOn

/-- Every jet through degree `s` of the Taylor polynomial agrees with the
corresponding jet of a smooth function at its center. -/
theorem iteratedFDeriv_finiteTaylorPolynomial_at {f : E → F}
    (hf : ContDiff ℝ ∞ f) {s i : ℕ} (hi : i ≤ s) (q : E) :
    iteratedFDeriv ℝ i (finiteTaylorPolynomial s f q) q = iteratedFDeriv ℝ i f q := by
  ext v
  rw [((finiteTaylorPolynomial_hasFiniteFPowerSeriesOnBall s f q).toHasFPowerSeriesOnBall).iteratedFDeriv_eq_sum
    (analyticOn_finiteTaylorPolynomial s f q) v]
  simp only [finiteTaylorSeries, ite_eq_left hi, ContinuousMultilinearMap.smul_apply]
  have hsym (σ : Perm (Fin i)) :
      iteratedFDeriv ℝ i f q (fun j => v (σ j)) = iteratedFDeriv ℝ i f q v :=
    iteratedFDeriv_comp_perm_of_contDiff hf i q v σ
  simp_rw [hsym]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr i.factorial_ne_zero), one_smul]

/-- Every derivative strictly above the degree of a finite Taylor
polynomial vanishes on the whole space. -/
theorem iteratedFDeriv_finiteTaylorPolynomial_eq_zero
    (s : ℕ) (f : E → F) (q : E) {i : ℕ} (hi : s < i) (z : E) :
    iteratedFDeriv ℝ i (finiteTaylorPolynomial s f q) z = 0 := by
  have hshift : HasFiniteFPowerSeriesOnBall (finiteTaylorPolynomial s f q)
      ((finiteTaylorSeries s f q).changeOrigin (z - q)) z (s + 1) ⊤ := by
    simpa using (finiteTaylorPolynomial_hasFiniteFPowerSeriesOnBall s f q).changeOrigin
      (y := z - q) (by simp)
  ext v
  rw [hshift.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
    (analyticOn_finiteTaylorPolynomial s f q) v]
  simp only [hshift.finite i (Nat.succ_le_of_lt hi),
    ContinuousMultilinearMap.zero_apply, Finset.sum_const_zero]

/-- The top derivative of a finite Taylor polynomial is constant everywhere
and equals the corresponding jet at the center. -/
theorem iteratedFDeriv_finiteTaylorPolynomial_top {f : E → F}
    (hf : ContDiff ℝ ∞ f) (s : ℕ) (q z : E) :
    iteratedFDeriv ℝ s (finiteTaylorPolynomial s f q) z = iteratedFDeriv ℝ s f q := by
  have htop : ContDiff ℝ ∞ (iteratedFDeriv ℝ s (finiteTaylorPolynomial s f q)) :=
    (contDiff_finiteTaylorPolynomial s f q (n := ∞)).iteratedFDeriv_right (by simp)
  have hzero : ∀ y, fderiv ℝ (iteratedFDeriv ℝ s (finiteTaylorPolynomial s f q)) y = 0 := by
    intro y
    rw [fderiv_iteratedFDeriv, Function.comp_apply,
      iteratedFDeriv_finiteTaylorPolynomial_eq_zero s f q (Nat.lt_succ_self s) y,
      LinearIsometryEquiv.map_zero]
  calc
    iteratedFDeriv ℝ s (finiteTaylorPolynomial s f q) z =
        iteratedFDeriv ℝ s (finiteTaylorPolynomial s f q) q :=
      is_const_of_fderiv_eq_zero (htop.differentiable (by simp)) hzero z q
    _ = iteratedFDeriv ℝ s f q := iteratedFDeriv_finiteTaylorPolynomial_at hf le_rfl q

/-- The constant top derivative inherits the exact bound of the input jet. -/
theorem norm_iteratedFDeriv_finiteTaylorPolynomial_top_le {f : E → F}
    (hf : ContDiff ℝ ∞ f) (s : ℕ) (q z : E) {M : ℝ}
    (hM : ‖iteratedFDeriv ℝ s f q‖ ≤ M) :
    ‖iteratedFDeriv ℝ s (finiteTaylorPolynomial s f q) z‖ ≤ M := by
  rw [iteratedFDeriv_finiteTaylorPolynomial_top hf s q z]
  exact hM

end ContinuousFlexibility.Analysis
