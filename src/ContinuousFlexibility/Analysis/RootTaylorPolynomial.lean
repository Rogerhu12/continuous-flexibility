import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Parity
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Polynomial terms under the root substitution

Symmetrizing a homogeneous multilinear Taylor term removes every odd power
of the root coordinate.  The remaining powers of `x ^ (3 / 2)` are ordinary
integer powers of `x`, giving a polynomial in the translated output variables.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology ContDiff

variable {n : ℕ}

/-- Slots of a Taylor coefficient after choosing which arguments contain the
root coordinate. -/
def rootTaylorSlots (S : Finset (Fin n)) (h : ℝ × ℝ) (i : Fin n) : ℝ × ℝ × ℝ :=
  if i ∈ S then (0, 1, 0) else (h.1, 0, h.2)

/-- The polynomial obtained by symmetrizing one homogeneous Taylor term.
The first output coordinate is translated by `x₀`. -/
def rootTaylorPolynomial
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ)
    (x₀ : ℝ) (h : ℝ × ℝ) : ℝ :=
  ∑ S : Finset (Fin n), if Even S.card then
    (x₀ + h.1) ^ (3 * (S.card / 2)) * A (rootTaylorSlots S h) else 0

/-- Multilinearity expands a root-coordinate translate by the subset of
slots which contribute that coordinate. -/
theorem multilinear_root_expansion
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ)
    (h : ℝ × ℝ) (ζ : ℝ) :
    A (fun _ => (h.1, ζ, h.2)) =
      ∑ S : Finset (Fin n), ζ ^ S.card * A (rootTaylorSlots S h) := by
  classical
  have hvec : (fun _ : Fin n => (h.1, ζ, h.2)) =
      (fun _ : Fin n => ζ • (0, 1, 0 : ℝ × ℝ × ℝ)) +
        (fun _ : Fin n => (h.1, 0, h.2)) := by
    ext i <;> simp
  rw [hvec, A.map_add_univ]
  apply Finset.sum_congr rfl
  intro S _
  have hslots :
      S.piecewise (fun _ => ζ • (0, 1, 0 : ℝ × ℝ × ℝ))
          (fun _ => (h.1, 0, h.2)) =
        S.piecewise (fun i => ζ • rootTaylorSlots S h i) (rootTaylorSlots S h) := by
    funext i
    by_cases hi : i ∈ S <;> simp [rootTaylorSlots, hi]
  rw [hslots, A.map_piecewise_smul]
  simp only [Finset.prod_const, smul_eq_mul]

/-- Even powers of the root parameter are ordinary integer powers. -/
theorem root_rpow_pow_of_even {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : Even k) :
    (x ^ (3 / 2 : ℝ)) ^ k = x ^ (3 * (k / 2)) := by
  have hsquare : (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ (3 : ℕ) := by
    calc
      (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ ((3 / 2 : ℝ) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hx (3 / 2) 2).symm
      _ = x ^ (3 : ℝ) := by norm_num
      _ = x ^ (3 : ℕ) := Real.rpow_natCast x 3
  obtain ⟨j, hj⟩ := hk
  have hkj : k = 2 * j := by omega
  have hdiv : k / 2 = j := by omega
  rw [hdiv, hkj, pow_mul, hsquare, ← pow_mul]

/-- On the nonnegative halfspace the explicit polynomial equals the
symmetrized homogeneous Taylor term under the root substitution. -/
theorem rootTaylorPolynomial_eq_average
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ)
    (x₀ : ℝ) (h : ℝ × ℝ) (hx : 0 ≤ x₀ + h.1) :
    rootTaylorPolynomial A x₀ h =
      (A (fun _ => (h.1, (x₀ + h.1) ^ (3 / 2 : ℝ), h.2)) +
        A (fun _ => (h.1, -((x₀ + h.1) ^ (3 / 2 : ℝ)), h.2))) / 2 := by
  classical
  symm
  rw [multilinear_root_expansion, multilinear_root_expansion,
    ← Finset.sum_add_distrib, Finset.sum_div]
  unfold rootTaylorPolynomial
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : Even S.card
  · rw [if_pos hS, hS.neg_pow, root_rpow_pow_of_even hx hS]
    ring
  · have hodd : Odd S.card := Nat.not_even_iff_odd.mp hS
    rw [if_neg hS, hodd.neg_pow]
    ring

/-- Each slot map is affine, hence smooth. -/
theorem contDiff_rootTaylorSlots (S : Finset (Fin n)) :
    ContDiff ℝ ∞ (rootTaylorSlots S) := by
  classical
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i ∈ S
  · simp only [rootTaylorSlots, if_pos hi]
    exact contDiff_const
  · simp only [rootTaylorSlots, if_neg hi]
    exact contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)

/-- The symmetrized Taylor term has a globally smooth polynomial extension. -/
theorem contDiff_rootTaylorPolynomial
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ) (x₀ : ℝ) :
    ContDiff ℝ ∞ (rootTaylorPolynomial A x₀) := by
  classical
  unfold rootTaylorPolynomial
  apply ContDiff.sum
  intro S _
  by_cases hS : Even S.card
  · simp only [if_pos hS]
    exact ((contDiff_const.add contDiff_fst).pow _).mul
      (A.contDiff.comp (contDiff_rootTaylorSlots S))
  · simp only [if_neg hS]
    exact contDiff_const

/-- Restricting a smooth function to one factor of a product does not
increase the norm of any iterated derivative. -/
theorem norm_iteratedFDeriv_prod_right_le
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P × E → F} (hf : ContDiff ℝ ∞ f) (p : P) (x : E) (s : ℕ) :
    ‖iteratedFDeriv ℝ s (fun y => f (p, y)) x‖ ≤
      ‖iteratedFDeriv ℝ s f (p, x)‖ := by
  let L : E →ₗᵢ[ℝ] P × E := LinearIsometry.inr ℝ P E
  have hshift : ContDiff ℝ ∞ (fun z : P × E => f ((p, 0) + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have heq : (fun y => f (p, y)) =
      (fun z : P × E => f ((p, 0) + z)) ∘ L.toContinuousLinearMap := by
    funext y
    simp only [Function.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      L, LinearIsometry.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  rw [heq, L.toContinuousLinearMap.iteratedFDeriv_comp_right hshift x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl s)]
  calc
    ‖(iteratedFDeriv ℝ s (fun z : P × E => f ((p, 0) + z)) (L x)).
        compContinuousLinearMap (fun _ => L.toContinuousLinearMap)‖ ≤
        ‖iteratedFDeriv ℝ s (fun z : P × E => f ((p, 0) + z)) (L x)‖ :=
      ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => L)
    _ = ‖iteratedFDeriv ℝ s f (p, x)‖ := by
      rw [iteratedFDeriv_comp_add_left]
      simp only [L, LinearIsometry.inr_apply, Prod.mk_add_mk, add_zero, zero_add]

/-- On a compact set, composing a multilinear coefficient with one fixed
smooth map bounds every fixed-order jet linearly in the coefficient norm.
No finite-dimensional assumption on the coefficient space is needed. -/
theorem exists_multilinear_comp_jet_bound
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ}
    {u : E → (Fin m → V)} (hu : ContDiff ℝ ∞ u)
    {K : Set E} (hK : IsCompact K) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : ContinuousMultilinearMap ℝ (fun _ : Fin m => V) ℝ,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ s (fun y => A (u y)) x‖ ≤ C * ‖A‖ := by
  classical
  have hJ : Continuous (fun x : E =>
      ∑ i ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ i u x‖) := by
    apply continuous_finsetSum
    intro i _
    exact (hu.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)).norm
  obtain ⟨b, hb⟩ := hK.bddAbove_image hJ.continuousOn
  let B : ℝ := max 1 b
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hBj (x : E) (hx : x ∈ K) (i : ℕ) (hi : i ≤ s) :
      ‖iteratedFDeriv ℝ i u x‖ ≤ B := by
    calc
      ‖iteratedFDeriv ℝ i u x‖ ≤
          ∑ j ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ j u x‖ :=
        Finset.single_le_sum (fun _ _ => norm_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      _ ≤ b := hb ⟨x, hx, rfl⟩
      _ ≤ B := le_max_right _ _
  let Q : ℝ := ∑ i ∈ Finset.range (s + 1),
    (m.descFactorial i : ℝ) * B ^ (m - i)
  have hQ0 : 0 ≤ Q :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB0 _))
  refine ⟨(s.factorial : ℝ) * Q * B ^ s,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hQ0) (pow_nonneg hB0 _), ?_⟩
  intro A x hx
  have hux : ‖u x‖ ≤ B := by
    simpa only [norm_iteratedFDeriv_zero] using hBj x hx 0 (Nat.zero_le s)
  have houter (i : ℕ) (hi : i ≤ s) :
      ‖iteratedFDeriv ℝ i A (u x)‖ ≤ Q * ‖A‖ := by
    calc
      ‖iteratedFDeriv ℝ i A (u x)‖ ≤
          (m.descFactorial i : ℝ) * ‖A‖ * ‖u x‖ ^ (m - i) := by
        simpa only [Fintype.card_fin] using A.norm_iteratedFDeriv_le i (u x)
      _ ≤ (m.descFactorial i : ℝ) * ‖A‖ * B ^ (m - i) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hux _)
          (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      _ = ((m.descFactorial i : ℝ) * B ^ (m - i)) * ‖A‖ := by ring
      _ ≤ Q * ‖A‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum
          (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB0 _))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) (norm_nonneg _)
  have hinner (i : ℕ) (hi1 : 1 ≤ i) (his : i ≤ s) :
      ‖iteratedFDeriv ℝ i u x‖ ≤ B ^ i :=
    (hBj x hx i his).trans (le_self_pow₀ hB1 (Nat.one_le_iff_ne_zero.mp hi1))
  calc
    ‖iteratedFDeriv ℝ s (fun y => A (u y)) x‖ ≤
        (s.factorial : ℝ) * (Q * ‖A‖) * B ^ s :=
      norm_iteratedFDeriv_comp_le A.contDiff hu
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl s) x houter hinner
    _ = ((s.factorial : ℝ) * Q * B ^ s) * ‖A‖ := by ring

private def rootTaylorAugmentedCoefficient
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => ℝ × ℝ × ℝ) ℝ :=
  ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight A).uncurryLeft

private theorem rootTaylorAugmentedCoefficient_apply
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ)
    (c : ℝ) (v : Fin n → ℝ × ℝ × ℝ) :
    rootTaylorAugmentedCoefficient A (Fin.cons (c, 0, 0) v) = c * A v := by
  simp only [rootTaylorAugmentedCoefficient, ContinuousLinearMap.uncurryLeft_apply,
    Fin.cons_zero, Fin.tail_cons, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.fst_apply, smul_apply, smul_eq_mul]

private theorem norm_rootTaylorAugmentedCoefficient
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ) :
    ‖rootTaylorAugmentedCoefficient A‖ = ‖A‖ := by
  rw [rootTaylorAugmentedCoefficient, ContinuousLinearMap.uncurryLeft_norm,
    ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_fst, one_mul]

private def rootTaylorTermInput (S : Finset (Fin n))
    (q : ℝ × (ℝ × ℝ)) : Fin (n + 1) → ℝ × ℝ × ℝ :=
  Fin.cons ((q.1 + q.2.1) ^ (3 * (S.card / 2)), 0, 0) (rootTaylorSlots S q.2)

private theorem contDiff_rootTaylorTermInput (S : Finset (Fin n)) :
    ContDiff ℝ ∞ (rootTaylorTermInput S) := by
  classical
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [rootTaylorTermInput, Fin.cons_zero]
    fun_prop
  · simp only [rootTaylorTermInput, Fin.cons_succ, rootTaylorSlots]
    by_cases hj : j ∈ S <;> simp only [hj, if_true, if_false] <;> fun_prop

private theorem exists_rootTaylorTerm_jet_bound (S : Finset (Fin n)) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ,
      ∀ x₀ ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ s
          (fun h : ℝ × ℝ =>
            (x₀ + h.1) ^ (3 * (S.card / 2)) * A (rootTaylorSlots S h)) 0‖ ≤ C * ‖A‖ := by
  let K : Set (ℝ × (ℝ × ℝ)) :=
    (fun x₀ : ℝ => (x₀, (0 : ℝ × ℝ))) '' Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    isCompact_Icc.image (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC0, hC⟩ :=
    exists_multilinear_comp_jet_bound (contDiff_rootTaylorTermInput S) hK s
  refine ⟨C, hC0, ?_⟩
  intro A x₀ hx₀
  let H : ℝ × (ℝ × ℝ) → ℝ :=
    fun q => rootTaylorAugmentedCoefficient A (rootTaylorTermInput S q)
  have hH : ContDiff ℝ ∞ H :=
    (rootTaylorAugmentedCoefficient A).contDiff.comp (contDiff_rootTaylorTermInput S)
  have heq :
      (fun h : ℝ × ℝ =>
        (x₀ + h.1) ^ (3 * (S.card / 2)) * A (rootTaylorSlots S h)) =
      (fun h => H (x₀, h)) := by
    funext h
    simp only [H, rootTaylorTermInput, rootTaylorAugmentedCoefficient_apply]
  rw [heq]
  refine (norm_iteratedFDeriv_prod_right_le hH x₀ (0 : ℝ × ℝ) s).trans ?_
  simpa only [norm_rootTaylorAugmentedCoefficient] using
    hC (rootTaylorAugmentedCoefficient A) (x₀, (0 : ℝ × ℝ)) ⟨x₀, hx₀, rfl⟩

/-- Every fixed-order jet of the polynomial extension is bounded by a
constant times the norm of its multilinear coefficient, uniformly for
`x₀ ∈ [0, 1]`. -/
theorem exists_rootTaylorPolynomial_jet_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ × ℝ) ℝ,
      ∀ x₀ ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ s (rootTaylorPolynomial A x₀) 0‖ ≤ C * ‖A‖ := by
  classical
  choose C hC0 hC using fun S : Finset (Fin n) => exists_rootTaylorTerm_jet_bound S s
  have hsum : 0 ≤ ∑ S : Finset (Fin n), C S := Finset.sum_nonneg (fun S _ => hC0 S)
  refine ⟨1 + ∑ S : Finset (Fin n), C S, by linarith, ?_⟩
  intro A x₀ hx₀
  have hsmooth (S : Finset (Fin n)) :
      ContDiff ℝ ∞ (fun h : ℝ × ℝ => if Even S.card then
        (x₀ + h.1) ^ (3 * (S.card / 2)) * A (rootTaylorSlots S h) else 0) := by
    by_cases hS : Even S.card
    · simp only [if_pos hS]
      exact ((contDiff_const.add contDiff_fst).pow _).mul
        (A.contDiff.comp (contDiff_rootTaylorSlots S))
    · simp only [if_neg hS]
      exact contDiff_const
  unfold rootTaylorPolynomial
  rw [iteratedFDeriv_fun_sum_apply (fun S _ =>
    ((hsmooth S).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl s)).contDiffAt)]
  calc
    ‖∑ S : Finset (Fin n), iteratedFDeriv ℝ s
        (fun h : ℝ × ℝ => if Even S.card then
          (x₀ + h.1) ^ (3 * (S.card / 2)) * A (rootTaylorSlots S h) else 0) 0‖ ≤
        ∑ S : Finset (Fin n), ‖iteratedFDeriv ℝ s
          (fun h : ℝ × ℝ => if Even S.card then
            (x₀ + h.1) ^ (3 * (S.card / 2)) * A (rootTaylorSlots S h) else 0) 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ S : Finset (Fin n), C S * ‖A‖ := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : Even S.card
      · simpa only [if_pos hS] using hC S A x₀ hx₀
      · simp only [if_neg hS, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
        exact mul_nonneg (hC0 S) (norm_nonneg A)
    _ = (∑ S : Finset (Fin n), C S) * ‖A‖ := (Finset.sum_mul ..).symm
    _ ≤ (1 + ∑ S : Finset (Fin n), C S) * ‖A‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg A)

end ContinuousFlexibility.Analysis
