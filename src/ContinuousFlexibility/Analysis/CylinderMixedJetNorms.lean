import ContinuousFlexibility.Analysis.CylinderMixedJets
import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual mixed jets are bounded by the corresponding Fréchet jet

The coordinate word contains exactly the prescribed numbers of radial
and angular unit vectors. Evaluation on that word has norm at most the
multilinear operator norm, including at order zero.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

theorem abs_mixedDerivative_le_norm_iteratedFDeriv
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    |mixedDerivative a b f p| ≤ ‖iteratedFDeriv ℝ (a + b) f p‖ := by
  let w : Fin (a + b) → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1
  have hl (i : Fin a) : w (Fin.castAdd b i) = 0 := by
    change (if (i : ℕ) < a then (0 : Fin 2) else 1) = 0
    exact if_pos i.isLt
  have hr (i : Fin b) : w (Fin.natAdd a i) = 1 := by
    change (if a + (i : ℕ) < a then (0 : Fin 2) else 1) = 1
    exact if_neg (by omega)
  have hrad : (∑ i, if w i = 0 then 1 else 0) = a := by
    rw [Fin.sum_univ_add]
    simp [hl, hr]
  have hang : (∑ i, if w i = 0 then 0 else 1) = b := by
    rw [Fin.sum_univ_add]
    simp [hl, hr]
  have he := iteratedFDeriv_cylinderBasis_eq_mixedDerivative hU hf (a + b) hp w
  rw [hrad, hang] at he
  have hv (i : Fin (a + b)) : ‖cylinderBasisVector (w i)‖ = 1 := by
    unfold cylinderBasisVector
    split <;> norm_num [Prod.norm_mk]
  calc
    |mixedDerivative a b f p| =
        ‖iteratedFDeriv ℝ (a + b) f p (fun i => cylinderBasisVector (w i))‖ := by
      rw [he, Real.norm_eq_abs]
    _ ≤ ‖iteratedFDeriv ℝ (a + b) f p‖ *
        ∏ i, ‖cylinderBasisVector (w i)‖ :=
      (iteratedFDeriv ℝ (a + b) f p).le_opNorm _
    _ = _ := by simp only [hv, Finset.prod_const_one, mul_one]

end ContinuousFlexibility.Statements
