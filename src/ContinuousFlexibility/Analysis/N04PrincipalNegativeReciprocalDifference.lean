module

public import ContinuousFlexibility.Analysis.N04PrincipalNegativeReciprocalBounds
public import ContinuousFlexibility.Analysis.N04PrincipalWeightedLinear
public import ContinuousFlexibility.Analysis.N04PrincipalWeightedProduct

/-!
# The height weight in a reciprocal difference

The exact reciprocal difference is a product with one original
difference factor. The other two factors are full reciprocal fields.
Consequently the sampled height weight occurs exactly once.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U : Set X} {Ω : Set PolarPoint}

theorem n04PrincipalNegative_inverse_sub_identity
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    -(a - b) * a⁻¹ * b⁻¹ = a⁻¹ - b⁻¹ := by
  field_simp [ha, hb]
  <;> ring

/-- A reciprocal difference retains the complete external weight of
the original difference on the same open parameter domain. -/
theorem n04PrincipalNegative_reciprocalDifference_weightedTower
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase requestedBase : ℕ) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (E W : ι → ℝ) (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 < W m)
    (f : ι → X → PolarPoint → ℝ) (f₀ : ι → PolarPoint → ℝ)
    (RD : ∀ m, MixedJetRegularity U Ω (fun x q => f m x q - f₀ m q))
    (RI : ∀ m, MixedJetRegularity U Ω (fun x q => (f m x q)⁻¹))
    (RI₀ : ∀ m, MixedJetRegularity U Ω (fun _ q => (f₀ m q)⁻¹))
    (RDI : ∀ m, MixedJetRegularity U Ω
      (fun x q => (f m x q)⁻¹ - (f₀ m q)⁻¹))
    (hD : N04PrincipalWeightedTowerBounds p oldBase E W RD)
    (hRI : N04PrincipalWeightedTowerBounds p oldBase E (fun _ => 1) RI)
    (hRI₀ : N04PrincipalWeightedTowerBounds p oldBase E (fun _ => 1) RI₀)
    (hnonzero : ∀ m x, x ∈ U → ∀ q ∈ Ω, f m x q ≠ 0)
    (hrefnonzero : ∀ m q, q ∈ Ω → f₀ m q ≠ 0) :
    ∃ base : ℕ, max oldBase requestedBase ≤ base ∧
      N04PrincipalWeightedTowerBounds p base E W RDI := by
  let RN (m : ι) : MixedJetRegularity U Ω (fun x q => -(f m x q - f₀ m q)) :=
    (RD m).scalarComp hU hΩ isOpen_univ contDiff_neg.contDiffOn
      (fun _ _ _ _ => mem_univ _)
  have hN := n04Principal_weightedTower_neg p oldBase E W RD RN hD
  let ff : Fin 3 → ι → X → PolarPoint → ℝ :=
    Fin.cons (fun m x q => -(f m x q - f₀ m q))
      (Fin.cons (fun m x q => (f m x q)⁻¹)
        (fun _ : Fin 1 => fun m _ q => (f₀ m q)⁻¹))
  let WW : Fin 3 → ι → ℝ := Fin.cons W (fun _ _ => 1)
  let RR : ∀ i m, MixedJetRegularity U Ω (ff i m) :=
    Fin.cases (fun m => RN m)
      (Fin.cases (fun m => RI m) (fun _ m => RI₀ m))
  have hWW (i : Fin 3) (m : ι) : 0 < WW i m := by
    fin_cases i
    · exact hW m
    · exact zero_lt_one
    · exact zero_lt_one
  have hRR (i : Fin 3) : N04PrincipalWeightedTowerBounds p oldBase E (WW i) (RR i) := by
    fin_cases i
    · exact hN
    · exact hRI
    · exact hRI₀
  let RP (m : ι) : MixedJetRegularity U Ω (fun x q => ∏ i, ff i m x q) :=
    MixedJetRegularity.finiteComp (fun i => RR i m) hU hΩ isOpen_univ
      (show ContDiff ℝ ∞ (fun v : Fin 3 → ℝ => ∏ i, v i) from
        contDiff_prod (fun i _ => contDiff_apply ℝ ℝ i)).contDiffOn
      (fun _ _ _ _ => mem_univ _)
  have hproduct := n04Principal_weightedTower_product p hp hI oldBase requestedBase
    hU hΩ E WW hE hWW ff RR RP hRR
  let base : ℕ := hproduct.choose
  have hw : (fun m => ∏ i, WW i m) = W := by
    funext m
    simp only [WW, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Finset.prod_const_one, mul_one]
  have hb : N04PrincipalWeightedTowerBounds p base E W RP := by
    rw [← hw]
    exact hproduct.choose_spec.2
  refine ⟨base, hproduct.choose_spec.1, ?_⟩
  apply n04Principal_weightedTower_congr p base E W hΩ RP RDI ?_ hb
  intro m x hx q hq
  simpa only [ff, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.prod_univ_zero, mul_one, mul_assoc] using
      n04PrincipalNegative_inverse_sub_identity (hnonzero m x hx q hq) (hrefnonzero m q hq)

end ContinuousFlexibility.Analysis
