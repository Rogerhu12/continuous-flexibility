module

public import ContinuousFlexibility.Analysis.N06RootBoundaryJetComparison

/-!
# Quantitative bounds for the actual finite boundary formulas

Four applications of the finite Leibniz estimate suffice for all eight
root boundary formulas. Their cost is an explicit polynomial of degree
sixteen in the input bound. Thus a material bound for the genuine input
jets remains a material bound after the boundary recursion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

def n06RootBoundaryStep (n : ℕ) (M : ℝ) : ℝ :=
  32 * ((2 : ℝ) ^ (n + 4) * M ^ 2)

def n06RootBoundaryPolynomialCost (n : ℕ) (M : ℝ) : ℝ :=
  (32 * (2 : ℝ) ^ (n + 4)) ^ 15 * M ^ 16

private theorem n06_rootJetPair_congr
    {n : ℕ} {M δ : ℝ} {f g f' g' : ℝ → ℝ}
    (H : N06RootJetPair n M δ f g) (hf : f = f') (hg : g = g') :
    N06RootJetPair n M δ f' g' := by
  cases hf
  cases hg
  exact H

theorem n06RootBoundaryStep_ge (n : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    M ≤ n06RootBoundaryStep n M := by
  have hT : (1 : ℝ) ≤ 2 ^ (n + 4) := one_le_pow₀ (by norm_num)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hsq : M ≤ M ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hT (sq_nonneg M)
  dsimp only [n06RootBoundaryStep]
  nlinarith

private theorem n06_root_product_in_budget
    {n m : ℕ} (hm : m ≤ n + 3) {M δ : ℝ} (hδ : 0 ≤ δ)
    {f g h j : ℝ → ℝ} (H : N06RootJetPair m M δ f g) (J : N06RootJetPair m M δ h j) :
    N06RootJetPair m ((2 : ℝ) ^ (n + 4) * M ^ 2) δ
      (fun θ => f θ * h θ) (fun θ => g θ * j θ) := by
  apply (H.mul J hδ).enlarge hδ
  have ht : (2 : ℝ) ^ (m + 1) ≤ 2 ^ (n + 4) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ht H.nonneg) H.nonneg).trans_eq (by ring)

private theorem n06_root_boundary_stage_one
    (n : ℕ) {M δ : ℝ} (hδ : 0 ≤ δ) (v w : N06RootBoundaryInputs)
    (hv : ∀ i, N06RootJetPair (n + 3) M δ (v i) (w i)) :
    N06RootJetPair (n + 3) (n06RootBoundaryStep n M) δ
      (n06RootEvenFormula1 v) (n06RootEvenFormula1 w) ∧
    N06RootJetPair (n + 3) (n06RootBoundaryStep n M) δ
      (n06RootOddFormula0 v) (n06RootOddFormula0 w) := by
  let B := (2 : ℝ) ^ (n + 4) * M ^ 2
  have hB : 0 ≤ B := mul_nonneg (by positivity) (sq_nonneg _)
  have hbudget : B ≤ n06RootBoundaryStep n M := by
    change B ≤ 32 * B
    nlinarith only [hB]
  have hE := (n06_root_product_in_budget (n := n) le_rfl hδ (hv 0) (hv 8)).neg
  have hO := (n06_root_product_in_budget (n := n) le_rfl hδ (hv 4) (hv 8)).const_mul_le_one
    hδ (c := (2 / 3 : ℝ)) (by norm_num)
  constructor
  · exact hE.enlarge hδ hbudget
  · refine n06_rootJetPair_congr (hO.enlarge hδ hbudget) ?_ ?_ <;>
      funext θ <;> dsimp only [n06RootOddFormula0] <;> ring

private theorem n06_root_boundary_stage_two
    (n : ℕ) {M δ : ℝ} (hδ : 0 ≤ δ) (v w : N06RootBoundaryInputs)
    (hv : ∀ i, N06RootJetPair (n + 2) M δ (v i) (w i))
    (hE : N06RootJetPair (n + 2) M δ
      (deriv (n06RootEvenFormula1 v)) (deriv (n06RootEvenFormula1 w)))
    (hO : N06RootJetPair (n + 2) M δ
      (deriv (n06RootOddFormula0 v)) (deriv (n06RootOddFormula0 w))) :
    N06RootJetPair (n + 2) (n06RootBoundaryStep n M) δ
      (n06RootEvenFormula2 v) (n06RootEvenFormula2 w) ∧
    N06RootJetPair (n + 2) (n06RootBoundaryStep n M) δ
      (n06RootOddFormula1 v) (n06RootOddFormula1 w) := by
  let B := (2 : ℝ) ^ (n + 4) * M ^ 2
  have hB : 0 ≤ B := mul_nonneg (by positivity) (sq_nonneg _)
  have hp := @n06_root_product_in_budget n (n + 2) (by omega) M δ hδ
  have he := ((hp (hv 0) hE).add (hp (hv 1) (hv 8))).neg
  have ho := (((hp (hv 4) hE).add (hp (hv 5) (hv 8))).sub
    (hp (hv 0) hO)).const_mul_le_one hδ (c := (2 / 5 : ℝ)) (by norm_num)
  constructor
  · exact he.enlarge hδ (by change B + B ≤ 32 * B; nlinarith only [hB])
  · exact ho.enlarge hδ (by change (B + B) + B ≤ 32 * B; nlinarith only [hB])

private theorem n06_root_boundary_stage_three
    (n : ℕ) {M δ : ℝ} (hδ : 0 ≤ δ) (v w : N06RootBoundaryInputs)
    (hv : ∀ i, N06RootJetPair (n + 1) M δ (v i) (w i))
    (hE₁ : N06RootJetPair (n + 1) M δ
      (deriv (n06RootEvenFormula1 v)) (deriv (n06RootEvenFormula1 w)))
    (hE₂ : N06RootJetPair (n + 1) M δ
      (deriv (n06RootEvenFormula2 v)) (deriv (n06RootEvenFormula2 w)))
    (hO₀ : N06RootJetPair (n + 1) M δ
      (deriv (n06RootOddFormula0 v)) (deriv (n06RootOddFormula0 w)))
    (hO₁ : N06RootJetPair (n + 1) M δ
      (deriv (n06RootOddFormula1 v)) (deriv (n06RootOddFormula1 w))) :
    N06RootJetPair (n + 1) (n06RootBoundaryStep n M) δ
      (n06RootEvenFormula3 v) (n06RootEvenFormula3 w) ∧
    N06RootJetPair (n + 1) (n06RootBoundaryStep n M) δ
      (n06RootOddFormula2 v) (n06RootOddFormula2 w) := by
  let B := (2 : ℝ) ^ (n + 4) * M ^ 2
  have hB : 0 ≤ B := mul_nonneg (by positivity) (sq_nonneg _)
  have hp := @n06_root_product_in_budget n (n + 1) (by omega) M δ hδ
  have he := ((((hp (hv 0) hE₂).add ((hp (hv 1) hE₁).const_mul 2)).add
    (hp (hv 2) (hv 8))).neg).add ((hp (hv 4) hO₀).const_mul 2)
  have ho := ((((hp (hv 4) hE₂).add ((hp (hv 5) hE₁).const_mul 2)).add
    (hp (hv 6) (hv 8))).sub
      (((hp (hv 0) hO₁).add (hp (hv 1) hO₀)).const_mul 2)).const_mul_le_one
        hδ (c := (2 / 7 : ℝ)) (by norm_num)
  constructor
  · have H := he.enlarge hδ (R := n06RootBoundaryStep n M) (by
      change ((B + |(2 : ℝ)| * B) + B) + |(2 : ℝ)| * B ≤ 32 * B
      norm_num
      nlinarith only [hB])
    refine n06_rootJetPair_congr H ?_ ?_ <;>
      funext θ <;> dsimp only [n06RootEvenFormula3] <;> ring
  · have H := ho.enlarge hδ (R := n06RootBoundaryStep n M) (by
      change ((B + |(2 : ℝ)| * B) + B) + |(2 : ℝ)| * (B + B) ≤ 32 * B
      norm_num
      nlinarith only [hB])
    refine n06_rootJetPair_congr H ?_ ?_ <;>
      funext θ <;> dsimp only [n06RootOddFormula2] <;> ring

private theorem n06_root_boundary_stage_four
    (n : ℕ) {M δ : ℝ} (hδ : 0 ≤ δ) (v w : N06RootBoundaryInputs)
    (hv : ∀ i, N06RootJetPair n M δ (v i) (w i))
    (hE₁ : N06RootJetPair n M δ (deriv (n06RootEvenFormula1 v)) (deriv (n06RootEvenFormula1 w)))
    (hE₂ : N06RootJetPair n M δ (deriv (n06RootEvenFormula2 v)) (deriv (n06RootEvenFormula2 w)))
    (hE₃ : N06RootJetPair n M δ (deriv (n06RootEvenFormula3 v)) (deriv (n06RootEvenFormula3 w)))
    (hO₀ : N06RootJetPair n M δ (deriv (n06RootOddFormula0 v)) (deriv (n06RootOddFormula0 w)))
    (hO₁ : N06RootJetPair n M δ (deriv (n06RootOddFormula1 v)) (deriv (n06RootOddFormula1 w)))
    (hO₂ : N06RootJetPair n M δ (deriv (n06RootOddFormula2 v)) (deriv (n06RootOddFormula2 w))) :
    N06RootJetPair n (n06RootBoundaryStep n M) δ (n06RootEvenFormula4 v) (n06RootEvenFormula4 w) ∧
    N06RootJetPair n (n06RootBoundaryStep n M) δ (n06RootOddFormula3 v) (n06RootOddFormula3 w) := by
  let B := (2 : ℝ) ^ (n + 4) * M ^ 2
  have hB : 0 ≤ B := mul_nonneg (by positivity) (sq_nonneg _)
  have hp := @n06_root_product_in_budget n n (by omega) M δ hδ
  have he := (((((hp (hv 0) hE₃).add ((hp (hv 1) hE₂).const_mul 3)).add
    ((hp (hv 2) hE₁).const_mul 3)).add (hp (hv 3) (hv 8))).neg).add
      (((hp (hv 4) hO₁).add (hp (hv 5) hO₀)).const_mul 6)
  have ho := (((((hp (hv 4) hE₃).add ((hp (hv 5) hE₂).const_mul 3)).add
    ((hp (hv 6) hE₁).const_mul 3)).add (hp (hv 7) (hv 8))).sub
      ((((hp (hv 0) hO₂).add ((hp (hv 1) hO₁).const_mul 2)).add
        (hp (hv 2) hO₀)).const_mul 3)).const_mul_le_one hδ
          (c := (2 / 9 : ℝ)) (by norm_num)
  constructor
  · have H := he.enlarge hδ (R := n06RootBoundaryStep n M) (by
      change (((B + |(3 : ℝ)| * B) + |(3 : ℝ)| * B) + B) +
        |(6 : ℝ)| * (B + B) ≤ 32 * B
      norm_num
      nlinarith only [hB])
    refine n06_rootJetPair_congr H ?_ ?_ <;>
      funext θ <;> dsimp only [n06RootEvenFormula4] <;> ring
  · have H := ho.enlarge hδ (R := n06RootBoundaryStep n M) (by
      change (((B + |(3 : ℝ)| * B) + |(3 : ℝ)| * B) + B) +
        |(3 : ℝ)| * ((B + |(2 : ℝ)| * B) + B) ≤ 32 * B
      norm_num
      nlinarith only [hB])
    refine n06_rootJetPair_congr H ?_ ?_ <;>
      funext θ <;> dsimp only [n06RootOddFormula3] <;> ring

/-- All eight actual boundary expressions have a fixed, explicit
polynomial cost. Only n+3 angular jets of their nine inputs are needed. -/
theorem n06_rootBoundaryFormulas_jet_comparison
    (n : ℕ) {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (v w : N06RootBoundaryInputs)
    (hv : ∀ i, N06RootJetPair (n + 3) M δ (v i) (w i)) :
    let A := n06RootBoundaryPolynomialCost n M
    N06RootJetPair n A δ (n06RootEvenFormula1 v) (n06RootEvenFormula1 w) ∧
    N06RootJetPair n A δ (n06RootEvenFormula2 v) (n06RootEvenFormula2 w) ∧
    N06RootJetPair n A δ (n06RootEvenFormula3 v) (n06RootEvenFormula3 w) ∧
    N06RootJetPair n A δ (n06RootEvenFormula4 v) (n06RootEvenFormula4 w) ∧
    N06RootJetPair n A δ (n06RootOddFormula0 v) (n06RootOddFormula0 w) ∧
    N06RootJetPair n A δ (n06RootOddFormula1 v) (n06RootOddFormula1 w) ∧
    N06RootJetPair n A δ (n06RootOddFormula2 v) (n06RootOddFormula2 w) ∧
    N06RootJetPair n A δ (n06RootOddFormula3 v) (n06RootOddFormula3 w) := by
  let M₁ := n06RootBoundaryStep n M
  let M₂ := n06RootBoundaryStep n M₁
  let M₃ := n06RootBoundaryStep n M₂
  let M₄ := n06RootBoundaryStep n M₃
  have h₀₁ : M ≤ M₁ := n06RootBoundaryStep_ge n hM
  have h₁₂ : M₁ ≤ M₂ := n06RootBoundaryStep_ge n (hM.trans h₀₁)
  have h₂₃ : M₂ ≤ M₃ := n06RootBoundaryStep_ge n ((hM.trans h₀₁).trans h₁₂)
  have h₃₄ : M₃ ≤ M₄ := n06RootBoundaryStep_ge n (((hM.trans h₀₁).trans h₁₂).trans h₂₃)
  obtain ⟨hE₁, hO₀⟩ := n06_root_boundary_stage_one n hδ v w hv
  obtain ⟨hE₂, hO₁⟩ := n06_root_boundary_stage_two n hδ v w
    (fun i => ((hv i).restrict (by omega)).enlarge hδ h₀₁) hE₁.deriv hO₀.deriv
  obtain ⟨hE₃, hO₂⟩ := n06_root_boundary_stage_three n hδ v w
    (fun i => ((hv i).restrict (by omega)).enlarge hδ (h₀₁.trans h₁₂))
    ((hE₁.deriv.restrict (by omega)).enlarge hδ h₁₂) hE₂.deriv
    ((hO₀.deriv.restrict (by omega)).enlarge hδ h₁₂) hO₁.deriv
  obtain ⟨hE₄, hO₃⟩ := n06_root_boundary_stage_four n hδ v w
    (fun i => ((hv i).restrict (by omega)).enlarge hδ ((h₀₁.trans h₁₂).trans h₂₃))
    ((hE₁.deriv.restrict (by omega)).enlarge hδ (h₁₂.trans h₂₃))
    ((hE₂.deriv.restrict (by omega)).enlarge hδ h₂₃) hE₃.deriv
    ((hO₀.deriv.restrict (by omega)).enlarge hδ (h₁₂.trans h₂₃))
    ((hO₁.deriv.restrict (by omega)).enlarge hδ h₂₃) hO₂.deriv
  have hcost : M₄ = n06RootBoundaryPolynomialCost n M := by
    dsimp only [M₄, M₃, M₂, M₁, n06RootBoundaryStep, n06RootBoundaryPolynomialCost]
    ring
  dsimp only
  rw [← hcost]
  exact ⟨(hE₁.restrict (by omega)).enlarge hδ ((h₁₂.trans h₂₃).trans h₃₄),
    (hE₂.restrict (by omega)).enlarge hδ (h₂₃.trans h₃₄),
    (hE₃.restrict (by omega)).enlarge hδ h₃₄, hE₄,
    (hO₀.restrict (by omega)).enlarge hδ ((h₁₂.trans h₂₃).trans h₃₄),
    (hO₁.restrict (by omega)).enlarge hδ (h₂₃.trans h₃₄),
    (hO₂.restrict (by omega)).enlarge hδ h₃₄, hO₃⟩

end ContinuousFlexibility.Analysis
