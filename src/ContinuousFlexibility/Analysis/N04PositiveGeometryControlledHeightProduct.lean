module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryKernelBounds
public import ContinuousFlexibility.Analysis.N06BoundaryRadialJets
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The finite radial product in the actual height

The fixed reference factor contributes ordinary scalar coefficients.
Only the odd and discriminant traces carry state and angle variables.
The exact double Leibniz sum preserves every reserved angular order and
the original parameter-height weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def n04PositiveGeometry_rootHeightProductTrace (n : ℕ) (a f g : ℕ → ℝ) : ℝ :=
  ∑ c : (Σ j : Fin (n + 1), Fin (n - j.val + 1)),
    ((n.choose c.1.val : ℝ) * ((n - c.1.val).choose c.2.val : ℝ) * a c.1.val) *
      (f c.2.val * g (n - c.1.val - c.2.val))

theorem n04PositiveGeometry_radialBoundaryJet_threeFactors
    {a : ℝ → ℝ} {f g : PolarPoint → ℝ} {θ : ℝ}
    (ha : ContDiffAt ℝ ∞ a 0) (hf : ContDiffAt ℝ ∞ f (0, θ))
    (hg : ContDiffAt ℝ ∞ g (0, θ)) (n : ℕ) :
    radialBoundaryJet (fun p => a p.1 * (f p * g p)) 0 n θ =
      n04PositiveGeometry_rootHeightProductTrace n (fun j => iteratedDeriv j a 0)
        (fun j => radialBoundaryJet f 0 j θ) (fun j => radialBoundaryJet g 0 j θ) := by
  classical
  have hf' : ContDiffAt ℝ ∞ (fun x : ℝ => f (x, θ)) 0 :=
    hf.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hg' : ContDiffAt ℝ ∞ (fun x : ℝ => g (x, θ)) 0 :=
    hg.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  simp only [radialBoundaryJet, n04PositiveGeometry_rootHeightProductTrace]
  rw [iteratedDeriv_fun_mul (ha.of_le (by simp))
    ((hf'.mul hg').of_le (by simp)), Fintype.sum_sigma,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDeriv_fun_mul (hf'.of_le (by simp)) (hg'.of_le (by simp)),
    ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def n04PositiveGeometry_rootHeightProductTrace_joint
    {U : Set E} (hU : IsOpen U) {n : ℕ} (a : ℕ → ℝ)
    {f g : ℕ → E × ℝ → ℝ}
    (J : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ) (f j))
    (Q : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ) (g j)) :
    SmoothDirections (U ×ˢ univ) (fun y =>
      n04PositiveGeometry_rootHeightProductTrace n a (fun j => f j y) (fun j => g j y)) := by
  classical
  let JT (c : Σ j : Fin (n + 1), Fin (n - j.val + 1)) :=
    smoothDirections_postcompCLM
      ((J c.2.val (by omega)).mul (Q (n - c.1.val - c.2.val) (by omega)))
      (((n.choose c.1.val : ℝ) * ((n - c.1.val).choose c.2.val : ℝ) * a c.1.val) •
        ContinuousLinearMap.id ℝ ℝ)
  exact smoothDirections_finiteSum (hU.prod isOpen_univ) JT

/-- A fixed finite polynomial cost for the two state-dependent factors
and the fixed reference jet. No angular reserve is spent here. -/
theorem n04PositiveGeometry_rootHeightProductTrace_word_bound
    (n N : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {U : Set E}, IsOpen U → ∀ (a : ℕ → ℝ) {f g : ℕ → E × ℝ → ℝ},
      ∀ J : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ) (f j),
      ∀ Q : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ) (g j),
      ∀ HJ : SmoothDirections (U ×ˢ univ) (fun y =>
        n04PositiveGeometry_rootHeightProductTrace n a (fun j => f j y) (fun j => g j y)),
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ j, j ≤ n → |a j| ≤ M) →
      (∀ j (hj : j ≤ n), N04BoundaryWordBounds (J j hj) K s d x θ P M H t shift) →
      (∀ j (hj : j ≤ n), N04BoundaryWordBounds (Q j hj) K s d x θ P M H t shift) →
      N04BoundaryWordBounds HJ K s d x θ P (C * M ^ (N + 3)) H t shift := by
  classical
  let mulData := n04PositiveGeometry_boundaryWord_mul (E := E) N L hL
  let Cmul : ℝ := mulData.choose
  have hCmul : 1 ≤ Cmul := mulData.choose_spec.1
  let I := Σ j : Fin (n + 1), Fin (n - j.val + 1)
  let coeff (c : I) : ℝ :=
    (n.choose c.1.val : ℝ) * ((n - c.1.val).choose c.2.val : ℝ)
  have hc (c : I) : 0 ≤ coeff c := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let C₀ : ℝ := 1 + ∑ c : I, coeff c
  have hC₀ : 1 ≤ C₀ := le_add_of_nonneg_right (Finset.sum_nonneg (fun c _ => hc c))
  have hcoeff (c : I) : coeff c ≤ C₀ :=
    (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ c)).trans
      (le_add_of_nonneg_left zero_le_one)
  let count : ℝ := Fintype.card I
  have hcount : 0 ≤ count := Nat.cast_nonneg _
  refine ⟨(1 + count) * (C₀ * Cmul), one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_right hcount) (one_le_mul_of_one_le_of_one_le hC₀ hCmul), ?_⟩
  intro U hU a f g J Q HJ K s d hN x hx θ P M H t hM hH hHL ht shift ha hf hg
  let JT (c : I) := smoothDirections_postcompCLM
    ((J c.2.val (by omega)).mul (Q (n - c.1.val - c.2.val) (by omega)))
    ((coeff c * a c.1.val) • ContinuousLinearMap.id ℝ ℝ)
  have hterm (c : I) : N04BoundaryWordBounds (JT c) K s d x θ P
      ((C₀ * Cmul) * M ^ (N + 3)) H t shift := by
    have hp := mulData.choose_spec.2 (J c.2.val (by omega))
      (Q (n - c.1.val - c.2.val) (by omega))
      K s d hN x hx θ P M H t hM hH hHL ht shift (hf _ _) (hg _ _)
    have hs := hp.scale (coeff c * a c.1.val)
    apply hs.enlarge hH (zero_le_one.trans ht)
    have hscalar : |coeff c * a c.1.val| ≤ C₀ * M := by
      rw [abs_mul, abs_of_nonneg (hc c)]
      exact mul_le_mul (hcoeff c) (ha _ (by omega)) (abs_nonneg _) (zero_le_one.trans hC₀)
    calc
      _ ≤ (C₀ * M) * (Cmul * M ^ (N + 2)) :=
        mul_le_mul_of_nonneg_right hscalar
          (mul_nonneg (zero_le_one.trans hCmul) (pow_nonneg (zero_le_one.trans hM) _))
      _ = _ := by rw [show N + 3 = N + 2 + 1 by omega, pow_succ]; ring
  have hsum := (N04BoundaryWordBounds.finiteSum hU JT hterm).congr (Q := HJ)
    hx (fun _ _ => rfl)
  apply hsum.enlarge hH (zero_le_one.trans ht)
  change count * ((C₀ * Cmul) * M ^ (N + 3)) ≤
    ((1 + count) * (C₀ * Cmul)) * M ^ (N + 3)
  nlinarith only [mul_nonneg (mul_nonneg (zero_le_one.trans hC₀)
    (zero_le_one.trans hCmul)) (pow_nonneg (zero_le_one.trans hM) (N + 3))]

end ContinuousFlexibility.Analysis
