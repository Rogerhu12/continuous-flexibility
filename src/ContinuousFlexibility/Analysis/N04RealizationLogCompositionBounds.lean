module

public import ContinuousFlexibility.Analysis.N04RealizationFiniteScalarComposition
public import ContinuousFlexibility.Analysis.N04RealizationLogScalarBounds

/-!
# Finite logarithmic compositions with one spatial scale

The outer logarithm derivatives are bounded by the actual positive
value and its reciprocal. The existing finite composition rule then
keeps every spatial order in its own power. Constants precede the
field, state, direction predicate and numerical envelope.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_logComposition_prefix_bound (n K s : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ (f : X → PolarPoint → ℝ) (F : MixedJetRegularity U Ω f),
      (∀ y ∈ U, ∀ q ∈ Ω, 0 < f y q) →
      ∀ q (hq : q ∈ Ω), ∀ x ∈ U, ∀ P : X → Prop,
      ∀ H M t : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ t → (f x q)⁻¹ ≤ M →
      (∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s →
        ∀ z : Fin j → X, (∀ i, P (z i)) →
        ‖(F.parameter u w q hq).D j x z‖ ≤
          M * parameterHeightWeight H j * t ^ (u + w)) →
      ∀ m : ℕ, m ≤ n → ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
      ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun p => iteratedDeriv m Real.log (f y p)) q),
      ∀ v : Fin k → X, (∀ i, P (v i)) →
      ‖J.D k x v‖ ≤ B * M ^ d * parameterHeightWeight H k * t ^ (a + b) := by
  classical
  obtain ⟨Clog, hClog, hlogb⟩ := n04Realization_log_outer_derivatives (n + K + s)
  let I : Type := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  choose c hc hcb using fun i : I =>
    n04Realization_finiteScalarComposition_bound (X := X) i.1.val i.2.1.val i.2.2.val RH
  let C : ℝ := 1 + ∑ i : I, c i
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hc i)))
  have hcC (i : I) : c i ≤ C :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  let L : ℕ := 2 * (n + K + s) + 1
  let N : ℕ := K + s + 1
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hN : 1 ≤ N := by dsimp only [N]; omega
  refine ⟨C * Clog ^ N, L * N,
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hClog),
    by simpa only [Nat.one_mul] using Nat.mul_le_mul hL hN, ?_⟩
  intro U hU Ω hΩ f F hpos q hq x hx P H M t hH hHR hM ht hinv hsource
    m hm k hk a b hab J v hv
  let M1 : ℝ := Clog * M ^ L
  have hM1 : 1 ≤ M1 := one_le_mul_of_one_le_of_one_le hClog (one_le_pow₀ hM)
  have hMM1 : M ≤ M1 := by
    calc
      M ≤ M ^ L := by
        simpa only [pow_one] using pow_le_pow_right₀ hM hL
      _ ≤ M1 := le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hM) _) hClog
  have hval : f x q ≤ M := by
    have h := hsource 0 (Nat.zero_le K) 0 0 (Nat.zero_le s)
      Fin.elim0 (fun i => i.elim0)
    have hn : |f x q| ≤ M := by
      simpa only [smoothDirections_D_zero_apply (F.parameter 0 0 q hq) hx,
        mixedDerivative, iteratedDeriv_zero, parameterHeightWeight, ite_true,
        Nat.add_zero, pow_zero, mul_one, Real.norm_eq_abs] using h
    exact (le_abs_self _).trans hn
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    fun y hy => (Real.contDiffAt_log.mpr hy.ne').contDiffWithinAt
  have houter (u : ℕ) (hu : u ≤ a + b) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (iteratedDeriv u (iteratedDeriv m Real.log)) (f x q)‖ ≤ M1 := by
    rw [circle_iteratedDeriv_iteratedDeriv]
    exact hlogb M (f x q) hM (hpos x hx q hq) hval hinv j (u + m) (by omega)
  have hsource' (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ a + b)
      (z : Fin j → X) (hz : ∀ i, P (z i)) :
      ‖(F.parameter u w q hq).D j x z‖ ≤
        M1 * parameterHeightWeight H j * t ^ (u + w) := by
    exact (hsource j (hj.trans hk) u w (huw.trans hab) z hz).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMM1 (parameterHeightWeight_nonneg hH j))
        (pow_nonneg (zero_le_one.trans ht) _))
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩,
    ⟨a, by omega⟩, ⟨b, by omega⟩)
  have h := hcb i U hU Ω hΩ (Ioi (0 : ℝ)) isOpen_Ioi f (iteratedDeriv m Real.log)
    F (contDiffOn_iteratedDeriv_open isOpen_Ioi hlog m)
    (fun y hy p hp => hpos y hy p hp) q hq J x hx P v hv
    H M1 t hH hHR hM1 ht houter hsource'
  have hcoef : c i * M1 ^ (k + a + b + 1) ≤ C * M1 ^ N :=
    mul_le_mul (hcC i) (pow_le_pow_right₀ hM1 (by dsimp only [N]; omega))
      (pow_nonneg (zero_le_one.trans hM1) _) (zero_le_one.trans hC)
  calc
    _ ≤ c i * M1 ^ (k + a + b + 1) * parameterHeightWeight H k * t ^ (a + b) := h
    _ ≤ C * M1 ^ N * parameterHeightWeight H k * t ^ (a + b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg hH k))
        (pow_nonneg (zero_le_one.trans ht) _)
    _ = _ := by
      dsimp only [M1]
      rw [mul_pow, ← pow_mul]
      ring

end ContinuousFlexibility.Analysis
