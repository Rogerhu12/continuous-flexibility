module

public import ContinuousFlexibility.Analysis.N04RealizationMixedProductJets
public import ContinuousFlexibility.Analysis.N04RealizationPotentialRegularity

/-!
# Raw differential-product bounds for the actual potential

The original divergence product rule gives seven terms; the mixed term
has coefficient two. Each term has three raw factors and exactly two
spatial derivatives before the requested outer derivatives. The genuine
parameter product bound is applied at that full spatial budget.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- The five actual scalar inputs to the reciprocal-height expression. -/
def n04RealizationPotentialInputs (A : SymmetricCoefficients)
    (H Q : PolarPoint → ℝ) : Fin 5 → PolarPoint → ℝ :=
  ![H, A.a, A.b, A.c, Q]

private def potentialSlots (t : Fin 7) : Fin 3 → Fin 5 :=
  ![0, (![1, 2, 3, 1, 2, 2, 3] : Fin 7 → Fin 5) t, 4]

private def potentialRadial : Fin 7 → Fin 3 → ℕ :=
  ![![0, 0, 2], ![0, 0, 1], ![0, 0, 0], ![0, 1, 1],
    ![0, 0, 1], ![0, 1, 0], ![0, 0, 0]]

private def potentialAngular : Fin 7 → Fin 3 → ℕ :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 0, 2], ![0, 0, 0],
    ![0, 1, 0], ![0, 0, 1], ![0, 1, 1]]

private def potentialCoefficient : Fin 7 → ℝ := ![1, 2, 1, 1, 1, 1, 1]

private theorem potential_total_order (t : Fin 7) :
    (∑ i, (potentialRadial t i + potentialAngular t i)) = 2 := by
  fin_cases t <;> norm_num [potentialRadial, potentialAngular, Fin.sum_univ_succ]

private theorem potential_coefficient_mass :
    (∑ t : Fin 7, |potentialCoefficient t|) = 8 := by
  norm_num [potentialCoefficient, Fin.sum_univ_succ]

private theorem potential_product_expansion
    {Ω : Set PolarPoint} (hΩ : IsOpen Ω) (A : SymmetricCoefficients)
    (H Q : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ A.a Ω) (hb : ContDiffOn ℝ ∞ A.b Ω)
    (hc : ContDiffOn ℝ ∞ A.c Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {q : PolarPoint} (hq : q ∈ Ω) :
    H q * divergenceOperator A Q q = ∑ t : Fin 7, potentialCoefficient t *
      ∏ i : Fin 3, mixedDerivative (potentialRadial t i) (potentialAngular t i)
        (n04RealizationPotentialInputs A H Q (potentialSlots t i)) q := by
  have hr (f : PolarPoint → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) :
      radialPartial f q = mixedDerivative 1 0 f q := by
    simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using
      n07a_radialPartial_mixedDerivative_on hΩ hf 0 0 hq
  have ht (f : PolarPoint → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) :
      angularPartial f q = mixedDerivative 0 1 f q := by
    simpa only [spaces_mixedDerivative_zero] using
      n07a_angularPartial_zero_mixedDerivative_on hΩ hf 0 hq
  have hQr : ContDiffOn ℝ ∞ (radialPartial Q) Ω :=
    (hQ.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hQt : ContDiffOn ℝ ∞ (angularPartial Q) Ω :=
    (hQ.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hrr : radialPartial (radialPartial Q) q = mixedDerivative 2 0 Q q :=
    (hr _ hQr).trans (mixedDerivative_radialPartial hΩ hQ 1 0 hq)
  have hrt : angularPartial (radialPartial Q) q = mixedDerivative 1 1 Q q :=
    (ht _ hQr).trans (mixedDerivative_radialPartial hΩ hQ 0 1 hq)
  have htt : angularPartial (angularPartial Q) q = mixedDerivative 0 2 Q q :=
    (ht _ hQt).trans (mixedDerivative_angularPartial hΩ hQ 0 1 hq)
  have hd := divergence_expansion_of_coefficients
    ((ha.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp))
    ((hb.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp))
    ((hc.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp))
    ((hQ.contDiffAt (hΩ.mem_nhds hq)).of_le (by simp))
  change divergenceOperator A Q q = _ at hd
  rw [hrr, hrt, htt, hr A.a ha, ht A.b hb, hr A.b hb, ht A.c hc, hr Q hQ, ht Q hQ] at hd
  rw [hd]
  simp only [potentialCoefficient, potentialSlots, potentialRadial, potentialAngular,
    n04RealizationPotentialInputs, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.sum_univ_zero, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    spaces_mixedDerivative_zero, mul_one, one_mul, add_zero]
  ring

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Before multilinear normalization, the genuine potential jet has the
exact spatial exponent `(a+b+2)/(s+1)`. Only raw principal and pulled
height jets are inputs, and the finite parameter prefix is kept explicit. -/
theorem n04Realization_potential_parameter_bound (k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ U : Set X, IsOpen U →
      ∀ Ω : Set PolarPoint, IsOpen Ω → ∀ A : X → SymmetricCoefficients,
      ∀ H Q : X → PolarPoint → ℝ,
      ∀ RF : ∀ i : Fin 5, MixedJetRegularity U Ω
        (fun x => n04RealizationPotentialInputs (A x) (H x) (Q x) i),
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun p => H x p * divergenceOperator (A x) (Q x) p) q),
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ s : ℕ, a + b + 2 ≤ s →
      ∀ W E C P R : ℝ, 0 ≤ W → W ≤ RH → 1 ≤ E → 1 ≤ C → 0 ≤ P → 1 ≤ R →
      (∀ i : Fin 5, ∀ u w : ℕ, u + w ≤ s →
        ‖mixedDerivative u w (n04RealizationPotentialInputs (A x) (H x) (Q x) i) q‖ ≤
          C * E ^ P * R ^ (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      (∀ i : Fin 5, ∀ u w : ℕ, ∀ (huw : u + w ≤ s)
        (d : OrderedFinpartition k) (j : Fin d.length),
        ‖((RF i).parameter u w q hq).D (d.partSize j) x (v ∘ d.emb j)‖ ≤
          W * (C * E ^ P * R ^ (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1)))) →
      ‖J.D k x v‖ ≤ B * C ^ 3 * E ^ (P * 3) * parameterHeightWeight W k *
        R ^ (((a + b + 2 : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨B₀, hB₀, hb₀⟩ := n04Realization_shiftedProduct_parameter_bound (X := X) 3 k a b RH
  refine ⟨8 * B₀, mul_pos (by norm_num) hB₀, ?_⟩
  intro U hU Ω hΩ A H Q RF q hq J x hx v s hs W E C P R hW hWR hE hC hP hR hbase hjet
  let f : Fin 5 → X → PolarPoint → ℝ :=
    fun i y => n04RealizationPotentialInputs (A y) (H y) (Q y) i
  let row : Fin 7 → X → PolarPoint → ℝ := fun t y p => ∏ i : Fin 3,
    mixedDerivative (potentialRadial t i) (potentialAngular t i) (f (potentialSlots t i) y) p
  let RR : ∀ t : Fin 7, MixedJetRegularity U Ω (row t) := fun t =>
    n04Realization_mixedJetRegularity_shiftedProduct hU hΩ
      (fun i => RF (potentialSlots t i)) (potentialRadial t) (potentialAngular t)
  let JT : ∀ t : Fin 7, SmoothDirections U (fun y => mixedDerivative a b (row t y) q) :=
    fun t => (RR t).parameter a b q hq
  let M : ℝ := C ^ 3 * E ^ (P * 3) * parameterHeightWeight W k *
    R ^ (((a + b + 2 : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hC) _)
      (Real.rpow_nonneg (zero_le_one.trans hE) _)) (parameterHeightWeight_nonneg hW k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have ht (t : Fin 7) : ‖(JT t).D k x v‖ ≤ B₀ * M := by
    have htorder : a + b + ∑ i, (potentialRadial t i + potentialAngular t i) ≤ s := by
      rw [potential_total_order]
      exact hs
    have h := hb₀ (potentialRadial t) (potentialAngular t) U hU Ω hΩ
      (fun i => f (potentialSlots t i)) (fun i => RF (potentialSlots t i))
      q hq (JT t) x hx v s htorder W E C P R hW hWR hE hC hP hR
      (fun i u w huw => hbase (potentialSlots t i) u w huw)
      (fun i u w huw d j => hjet (potentialSlots t i) u w huw d j)
    simpa only [potential_total_order, Nat.cast_ofNat, M, mul_assoc] using h
  have hformula : ∀ y ∈ U,
      mixedDerivative a b (fun p => H y p * divergenceOperator (A y) (Q y) p) q =
        ∑ t : Fin 7, potentialCoefficient t * mixedDerivative a b (row t y) q := by
    intro y hy
    have he : EqOn (fun p => H y p * divergenceOperator (A y) (Q y) p)
        (fun p => ∑ t : Fin 7, potentialCoefficient t * row t y p) Ω := by
      intro p hp
      exact potential_product_expansion hΩ (A y) (H y) (Q y)
        ((RF 1).spatial y hy) ((RF 2).spatial y hy)
        ((RF 3).spatial y hy) ((RF 4).spatial y hy) hp
    rw [n07a_mixedDerivative_eqOn hΩ he a b hq,
      n07a_mixedDerivative_sum_on hΩ
        (fun t _ => contDiffOn_const.mul ((RR t).spatial y hy)) a b hq]
    apply Finset.sum_congr rfl
    intro t _
    exact spaces_mixedDerivative_const_mul (row t y) (potentialCoefficient t) a b q
  rw [smoothDirections_D_eq_linearCombination J JT potentialCoefficient hformula k hx v]
  calc
    ‖∑ t : Fin 7, potentialCoefficient t * (JT t).D k x v‖ ≤
        ∑ t : Fin 7, |potentialCoefficient t| * ‖(JT t).D k x v‖ := by
      simpa only [norm_mul, Real.norm_eq_abs] using
        norm_sum_le (Finset.univ : Finset (Fin 7))
          (fun t : Fin 7 => potentialCoefficient t * (JT t).D k x v)
    _ ≤ ∑ t : Fin 7, |potentialCoefficient t| * (B₀ * M) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (ht t) (abs_nonneg _))
    _ = 8 * B₀ * M := by rw [← Finset.sum_mul, potential_coefficient_mass]; ring
    _ = _ := by dsimp only [M]; ring

end ContinuousFlexibility.Analysis
