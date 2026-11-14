module

public import ContinuousFlexibility.Analysis.N06CubicLp
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Multiplication on the actual finite angular-jet L² space

The finite Leibniz formula and Cauchy--Schwarz give a multiplier bound
using only the coefficient derivatives through the fixed source order.
The measure is arbitrary, and every norm below is an actual L² norm of
`mixedDerivative 0 k`, rather than a replacement Fourier norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- A finite constant for the k-th Leibniz row. -/
def n06AngularLeibnizCost (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℝ) ^ 2

/-- The multiplier constant on all actual angular derivatives through b. -/
def n06AngularMultiplierCost (b : ℕ) : ℝ :=
  ∑ k : Fin (b + 1), n06AngularLeibnizCost k.val

theorem n06AngularLeibnizCost_nonneg (k : ℕ) : 0 ≤ n06AngularLeibnizCost k :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem n06AngularMultiplierCost_nonneg (b : ℕ) : 0 ≤ n06AngularMultiplierCost b :=
  Finset.sum_nonneg (fun _ _ => n06AngularLeibnizCost_nonneg _)

/-- Ordinary one-dimensional Leibniz gives the actual pure angular jet.
Only smoothness of the angular slices is needed. -/
theorem n06_angularJet_mul_formula (f g : PolarPoint → ℝ)
    (hf : ∀ r, ContDiff ℝ ∞ (fun θ => f (r, θ)))
    (hg : ∀ r, ContDiff ℝ ∞ (fun θ => g (r, θ))) (k : ℕ) (p : PolarPoint) :
    mixedDerivative 0 k (fun q => f q * g q) p =
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℝ) *
        mixedDerivative 0 i f p * mixedDerivative 0 (k - i) g p := by
  simpa only [mixedDerivative, iteratedDeriv_zero] using
    iteratedDeriv_fun_mul
      ((hf p.1).contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
      ((hg p.1).contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞)) (x := p.2)

/-- A coefficient small in all jets through b multiplies the k-th jet
without requiring any source derivative above b. -/
theorem n06_angularJet_mul_sq_le (f g : PolarPoint → ℝ)
    (hf : ∀ r, ContDiff ℝ ∞ (fun θ => f (r, θ)))
    (hg : ∀ r, ContDiff ℝ ∞ (fun θ => g (r, θ)))
    {b : ℕ} (k : Fin (b + 1)) (p : PolarPoint) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ j : Fin (b + 1), |mixedDerivative 0 j.val f p| ≤ δ) :
    (mixedDerivative 0 k.val (fun q => f q * g q) p) ^ 2 ≤
      (n06AngularLeibnizCost k.val * δ ^ 2) *
        ∑ j : Fin (b + 1), (mixedDerivative 0 j.val g p) ^ 2 := by
  let S := ∑ j : Fin (b + 1), (mixedDerivative 0 j.val g p) ^ 2
  have hsource (i : ℕ) : (mixedDerivative 0 (k.val - i) g p) ^ 2 ≤ S := by
    let j : Fin (b + 1) := ⟨k.val - i, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    exact Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (b + 1)))) =>
      sq_nonneg (mixedDerivative 0 j.val g p)) (Finset.mem_univ j)
  have hs : (∑ i ∈ Finset.range (k.val + 1),
      (mixedDerivative 0 (k.val - i) g p) ^ 2) ≤ ((k.val + 1 : ℕ) : ℝ) * S := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (k.val + 1), S :=
        Finset.sum_le_sum (fun i _ => hsource i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hc : (∑ i ∈ Finset.range (k.val + 1),
      (((k.val.choose i : ℕ) : ℝ) * mixedDerivative 0 i f p) ^ 2) ≤
      δ ^ 2 * ∑ i ∈ Finset.range (k.val + 1), ((k.val.choose i : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hib : i < b + 1 := by
      have hki := k.isLt
      have hii := Finset.mem_range.mp hi
      omega
    have hfi := hcoeff ⟨i, hib⟩
    have hsq : (mixedDerivative 0 i f p) ^ 2 ≤ δ ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (mixedDerivative 0 i f p)) hδ).mpr hfi
    calc
      _ = ((k.val.choose i : ℕ) : ℝ) ^ 2 * (mixedDerivative 0 i f p) ^ 2 := mul_pow _ _ _
      _ ≤ ((k.val.choose i : ℕ) : ℝ) ^ 2 * δ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = _ := by ring
  rw [n06_angularJet_mul_formula f g hf hg]
  calc
    _ ≤ (∑ i ∈ Finset.range (k.val + 1),
          (((k.val.choose i : ℕ) : ℝ) * mixedDerivative 0 i f p) ^ 2) *
        ∑ i ∈ Finset.range (k.val + 1), (mixedDerivative 0 (k.val - i) g p) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (δ ^ 2 * ∑ i ∈ Finset.range (k.val + 1), ((k.val.choose i : ℕ) : ℝ) ^ 2) *
        (((k.val + 1 : ℕ) : ℝ) * S) :=
      mul_le_mul hc hs (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by dsimp only [n06AngularLeibnizCost, S]; ring

/-- Actual L² membership and the whole fixed-order jet norm bound for
multiplication by a coefficient with small measurable angular jets. -/
theorem n06_angularJet_mul_lp_bound {μ : Measure PolarPoint}
    (f g : PolarPoint → ℝ)
    (hf : ∀ r, ContDiff ℝ ∞ (fun θ => f (r, θ)))
    (hg : ∀ r, ContDiff ℝ ∞ (fun θ => g (r, θ)))
    (b : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hfmeas : ∀ j : Fin (b + 1), AEStronglyMeasurable (mixedDerivative 0 j.val f) μ)
    (hgLp : ∀ j : Fin (b + 1), MemLp (mixedDerivative 0 j.val g) 2 μ)
    (hcoeff : ∀ᵐ p ∂μ, ∀ j : Fin (b + 1), |mixedDerivative 0 j.val f p| ≤ δ) :
    ∃ hmul : ∀ k : Fin (b + 1),
        MemLp (mixedDerivative 0 k.val (fun p => f p * g p)) 2 μ,
      (∑ k : Fin (b + 1),
        ‖(hmul k).toLp (mixedDerivative 0 k.val (fun p => f p * g p))‖ ^ 2) ≤
        (n06AngularMultiplierCost b * δ ^ 2) *
          ∑ j : Fin (b + 1), ‖(hgLp j).toLp (mixedDerivative 0 j.val g)‖ ^ 2 := by
  have hmeas (k : Fin (b + 1)) :
      AEStronglyMeasurable (mixedDerivative 0 k.val (fun p => f p * g p)) μ := by
    have heq : mixedDerivative 0 k.val (fun p => f p * g p) =
        fun p => ∑ i ∈ Finset.range (k.val + 1), ((k.val.choose i : ℕ) : ℝ) *
          mixedDerivative 0 i f p * mixedDerivative 0 (k.val - i) g p :=
      funext (n06_angularJet_mul_formula f g hf hg k.val)
    rw [heq]
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    have hib : i < b + 1 := by
      have hki := k.isLt
      have hii := Finset.mem_range.mp hi
      omega
    let j : Fin (b + 1) := ⟨k.val - i, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    exact (aestronglyMeasurable_const.mul (hfmeas ⟨i, hib⟩)).mul
      (hgLp j).aestronglyMeasurable
  have hrow (k : Fin (b + 1)) :=
    n06_memLp_of_square_le_finiteSum
      (fun j : Fin (b + 1) => mixedDerivative 0 j.val g)
      (K := n06AngularLeibnizCost k.val * δ ^ 2)
      (mul_nonneg (n06AngularLeibnizCost_nonneg _) (sq_nonneg _))
      (hmeas k) hgLp
      (hcoeff.mono (fun p hp => n06_angularJet_mul_sq_le f g hf hg k p hδ hp))
  choose hmul hsq hnorm using hrow
  refine ⟨hmul, ?_⟩
  calc
    _ ≤ ∑ k : Fin (b + 1), (n06AngularLeibnizCost k.val * δ ^ 2) *
        ∑ j : Fin (b + 1), ‖(hgLp j).toLp (mixedDerivative 0 j.val g)‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => hsq k)
    _ = _ := by simp only [n06AngularMultiplierCost, Finset.sum_mul]

end ContinuousFlexibility.Analysis
