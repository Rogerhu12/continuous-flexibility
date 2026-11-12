import ContinuousFlexibility.Analysis.FiniteInversePolynomialEnvelope
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Choose

/-!
# Finite inverse jets with a retained coefficient envelope

The state set and the physical domains are fixed before the requested
finite order. A first differential bound and finitely many positive jets
of the genuine inverse give a polynomial bound for the forward jets.
The coefficient weight remains explicit, and only its numerical exponent
and the finite state order grow. No value bound on either map is used.
-/

noncomputable section

universe u v w t

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff BigOperators

/-- Finite positive forward jets on an unchanged family of domains.
The state parameter is an abstract type; its only quantitative data are
the increasing scalar bounds rho. -/
theorem nonlinearInverse_finitePrefix_weighted_bound
    {E : Type u} {F : Type v} {Z : Type w} {I : Type t}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set Z) (Ω : Z → I → Set E) (W : I → ℝ) (rho : ℕ → Z → ℝ)
    (forward : Z → I → E → F) (inverse : Z → I → F → E)
    (dInv : ℕ) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (hW : ∀ m, 1 ≤ W m)
    (hrho : ∀ r z, z ∈ U → 1 ≤ rho r z)
    (hrhoMono : ∀ z ∈ U, Monotone (fun r => rho r z))
    (hforward : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      ContDiffAt ℝ ∞ (forward z m) x)
    (hinverse : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      ContDiffAt ℝ ∞ (inverse z m) (forward z m x))
    (hgerm : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      inverse z m ∘ forward z m =ᶠ[𝓝 x] (id : E → E))
    (hleft : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      (fderiv ℝ (forward z m) x).comp
          (fderiv ℝ (inverse z m) (forward z m x)) = ContinuousLinearMap.id ℝ F)
    (hfirst : ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
      ‖fderiv ℝ (forward z m) x‖ ≤ B₀ * W m ^ B₀)
    (hjets : ∀ n : ℕ, 2 ≤ n → ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ m x, x ∈ Ω z m →
        ‖iteratedFDeriv ℝ n (inverse z m) (forward z m x)‖ ≤
          B * W m ^ B * rho (n + dInv) z) :
    ∀ N : ℕ, ∃ d : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ z ∈ U, ∀ m x, x ∈ Ω z m → ∀ k : ℕ, 1 ≤ k → k ≤ N →
        ‖iteratedFDeriv ℝ k (forward z m) x‖ ≤
          C * W m ^ A * rho (N + dInv) z ^ d := by
  classical
  intro N
  choose c hc degree hpolynomial using fun i : Fin N =>
    exists_nonlinearInverse_finiteJet_polynomial_envelope (E := F) (F := E) i.val
  choose a ha hab using fun j : Fin (N - 1) =>
    hjets (j.val + 2) (by omega)
  let R : ℝ := 1 + B₀ + ∑ j : Fin (N - 1), a j
  have hsum : 0 ≤ ∑ j : Fin (N - 1), a j :=
    Finset.sum_nonneg (fun j _ => (ha j).le)
  have hR : 1 ≤ R := by
    dsimp only [R]
    linarith only [hB₀, hsum]
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hB₀R : B₀ ≤ R := by
    dsimp only [R]
    linarith only [hsum]
  have haR (j : Fin (N - 1)) : a j ≤ R := by
    have hj : a j ≤ ∑ l : Fin (N - 1), a l :=
      Finset.single_le_sum (fun l _ => (ha l).le) (Finset.mem_univ j)
    dsimp only [R]
    linarith only [hj, hB₀]
  let Cpoly : ℝ := 1 + ∑ i : Fin N, c i
  let d : ℕ := ∑ i : Fin N, degree i
  have hc0 (i : Fin N) : 0 ≤ c i := zero_le_one.trans (hc i)
  have hCpoly : 1 ≤ Cpoly :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hc0 i))
  have hcC (i : Fin N) : c i ≤ Cpoly :=
    (Finset.single_le_sum (fun j _ => hc0 j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdegree (i : Fin N) : degree i ≤ d :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (degree j)) (Finset.mem_univ i)
  refine ⟨d, Cpoly * R ^ d, R * (d : ℝ),
    mul_pos (zero_lt_one.trans_le hCpoly) (pow_pos hRpos d),
    mul_nonneg hR0 (Nat.cast_nonneg d), ?_⟩
  intro z hz m x hx k hk hkN
  let M : ℝ := R * W m ^ R * rho (N + dInv) z
  have hW0 : 0 ≤ W m := zero_le_one.trans (hW m)
  have hrho1 : 1 ≤ rho (N + dInv) z := hrho (N + dInv) z hz
  have hM : 1 ≤ M :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hR (Real.one_le_rpow (hW m) hR0)) hrho1
  have hcoefficient {B : ℝ} (hBR : B ≤ R) : B * W m ^ B ≤ R * W m ^ R :=
    mul_le_mul hBR (Real.rpow_le_rpow_of_exponent_le (hW m) hBR)
      (Real.rpow_nonneg hW0 B) hR0
  have hfirstM : ‖fderiv ℝ (forward z m) x‖ ≤ M :=
    (hfirst z hz m x hx).trans ((hcoefficient hB₀R).trans
      (le_mul_of_one_le_right
        (mul_nonneg hR0 (Real.rpow_nonneg hW0 R)) hrho1))
  let i : Fin N := ⟨k - 1, by omega⟩
  have hik : i.val + 1 = k := by
    dsimp only [i]
    omega
  have hraw (j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i.val) :
      ‖iteratedFDeriv ℝ (j + 1) (inverse z m) (forward z m x)‖ ≤ M := by
    have hjN : j + 1 ≤ N := by
      have hi := i.isLt
      omega
    let l : Fin (N - 1) := ⟨j - 1, by omega⟩
    have hlj : l.val + 2 = j + 1 := by
      dsimp only [l]
      omega
    have hin := hab l z hz m x hx
    rw [hlj] at hin
    exact hin.trans (mul_le_mul (hcoefficient (haR l))
      (hrhoMono z hz (Nat.add_le_add_right hjN dInv))
      (zero_le_one.trans (hrho (j + 1 + dInv) z hz))
      (mul_nonneg hR0 (Real.rpow_nonneg hW0 R)))
  have hb := hpolynomial i hM (inverse z m) (forward z m) x
    (hinverse z hz m x hx) (hforward z hz m x hx) (hgerm z hz m x hx)
    (fderiv ℝ (forward z m) x) (hleft z hz m x hx) hfirstM hraw
  have hb' : ‖iteratedFDeriv ℝ k (forward z m) x‖ ≤ c i * M ^ degree i := by
    simpa only [hik] using hb
  calc
    _ ≤ c i * M ^ degree i := hb'
    _ ≤ Cpoly * M ^ d :=
      mul_le_mul (hcC i) (pow_le_pow_right₀ hM (hdegree i))
        (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hCpoly)
    _ = (Cpoly * R ^ d) * W m ^ (R * (d : ℝ)) * rho (N + dInv) z ^ d := by
      dsimp only [M]
      rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hW0 R d]
      ring

end ContinuousFlexibility.Analysis
