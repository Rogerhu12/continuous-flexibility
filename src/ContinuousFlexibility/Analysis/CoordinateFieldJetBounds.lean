import ContinuousFlexibility.Analysis.CoordinatePotentialRegularity
import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction
import ContinuousFlexibility.Analysis.CylinderSobolev
import ContinuousFlexibility.Analysis.FlowJetMaterialClosure
import ContinuousFlexibility.Analysis.FlowJetPartitionPolynomial
import ContinuousFlexibility.Analysis.SpacesHeightAlgebra
import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets
import ContinuousFlexibility.Analysis.LocalMixedProductBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Fixed-loss raw-jet bounds for the actual transformed fields

Only the operations occurring in the actual potential and principal
density are expanded: addition, multiplication, and the two true
coordinate partial derivatives. Every resulting monomial has total
derivative weight at most the requested order plus two. The existing
interpolation theorem therefore selects one low order and one loss
before the output order, state, envelope, or coordinate fields.

The nine inputs below are actual coefficient functions, the four actual
first derivative components of the chart, the height, and the reciprocal
absolute actual Jacobian. The angular lift itself is not an input field.
No potential or transformed-coefficient jet bound is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators Topology

set_option backward.isDefEq.respectTransparency false

private inductive CanonicalRawExpr where
  | atom : Fin 9 → CanonicalRawExpr
  | add : CanonicalRawExpr → CanonicalRawExpr → CanonicalRawExpr
  | mul : CanonicalRawExpr → CanonicalRawExpr → CanonicalRawExpr
  | radial : CanonicalRawExpr → CanonicalRawExpr
  | angular : CanonicalRawExpr → CanonicalRawExpr

private def rawExprEval : CanonicalRawExpr → (Fin 9 → PolarPoint → ℝ) → PolarPoint → ℝ
  | .atom i, f => f i
  | .add e d, f => fun q => rawExprEval e f q + rawExprEval d f q
  | .mul e d, f => fun q => rawExprEval e f q * rawExprEval d f q
  | .radial e, f => radialPartial (rawExprEval e f)
  | .angular e, f => angularPartial (rawExprEval e f)

private def rawExprWeight : CanonicalRawExpr → ℕ
  | .atom _ => 0
  | .add e d => max (rawExprWeight e) (rawExprWeight d)
  | .mul e d => rawExprWeight e + rawExprWeight d
  | .radial e => rawExprWeight e + 1
  | .angular e => rawExprWeight e + 1

private theorem contDiff_rawExprEval (e : CanonicalRawExpr)
    {f : Fin 9 → PolarPoint → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (rawExprEval e f) := by
  induction e with
  | atom i => exact hf i
  | add e d he hd => exact he.add hd
  | mul e d he hd => exact he.mul hd
  | radial e he => exact contDiff_cylinder_radialPartial he
  | angular e he => exact contDiff_cylinder_angularPartial he

private theorem contDiffAt_rawExprEval (e : CanonicalRawExpr)
    {f : Fin 9 → PolarPoint → ℝ} {q : PolarPoint}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) q) :
    ContDiffAt ℝ ∞ (rawExprEval e f) q := by
  induction e with
  | atom i => exact hf i
  | add e d he hd => exact he.add hd
  | mul e d he hd => exact he.mul hd
  | radial e he =>
      exact (he.fderiv_right (by simp)).clm_apply
        (contDiffAt_const (c := ((1, 0) : PolarPoint)))
  | angular e he =>
      exact (he.fderiv_right (by simp)).clm_apply
        (contDiffAt_const (c := ((0, 1) : PolarPoint)))

private theorem rawExprEval_eventuallyEq (e : CanonicalRawExpr)
    {f g : Fin 9 → PolarPoint → ℝ} {q : PolarPoint}
    (hfg : ∀ i, f i =ᶠ[𝓝 q] g i) :
    rawExprEval e f =ᶠ[𝓝 q] rawExprEval e g := by
  induction e with
  | atom i => exact hfg i
  | add e d he hd => exact he.add hd
  | mul e d he hd => exact he.mul hd
  | radial e he =>
      exact (he.fderiv (𝕜 := ℝ)).mono fun y hy =>
        congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hy
  | angular e he =>
      exact (he.fderiv (𝕜 := ℝ)).mono fun y hy =>
        congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hy

private theorem rawExpr_mixed_majorant (e : CanonicalRawExpr) (a b : ℕ) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P (a + b + rawExprWeight e) ∧
      ∀ f : Fin 9 → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (f i)) →
      ∀ q : PolarPoint, ∀ X : ℕ → ℝ, (∀ k, 0 ≤ X k) →
        (∀ i a b, |mixedDerivative a b (f i) q| ≤ X (a + b)) →
        |mixedDerivative a b (rawExprEval e f) q| ≤ flowJetPolynomialEval P X := by
  classical
  induction e generalizing a b with
  | atom i =>
    refine ⟨[(1, [a + b])], FlowJetPolynomialDegreeLE.atom (a + b), ?_⟩
    intro f _ q X _ hraw
    simpa only [rawExprEval, flowJetPolynomialEval_atom] using hraw i a b
  | add e d he hd =>
    obtain ⟨P, hP, hbP⟩ := he a b
    obtain ⟨Q, hQ, hbQ⟩ := hd a b
    have hPm := hP.mono
      (Nat.add_le_add_left (le_max_left (rawExprWeight e) (rawExprWeight d)) (a + b))
    have hQm := hQ.mono
      (Nat.add_le_add_left (le_max_right (rawExprWeight e) (rawExprWeight d)) (a + b))
    refine ⟨P ++ Q, hPm.append hQm, ?_⟩
    intro f hf q X hX hraw
    change |mixedDerivative a b (fun p => rawExprEval e f p + rawExprEval d f p) q| ≤ _
    rw [spaces_mixedDerivative_add (contDiff_rawExprEval e hf) (contDiff_rawExprEval d hf),
      flowJetPolynomialEval_append]
    exact (abs_add_le _ _).trans (add_le_add (hbP f hf q X hX hraw) (hbQ f hf q X hX hraw))
  | mul e d he hd =>
    choose P hP hbP using he
    choose Q hQ hbQ using hd
    let R (j : Fin (b + 1)) (i : Fin (a + 1)) : FlowJetPolynomial :=
      flowJetPolynomialMul [((b.choose (j : ℕ) : ℝ) * (a.choose (i : ℕ) : ℝ), [])]
        (flowJetPolynomialMul (P i j) (Q (a - i) (b - j)))
    have hR (j : Fin (b + 1)) (i : Fin (a + 1)) :
        FlowJetPolynomialDegreeLE (R j i) (a + b + (rawExprWeight e + rawExprWeight d)) := by
      have hc : 0 ≤ (b.choose (j : ℕ) : ℝ) * (a.choose (i : ℕ) : ℝ) := by positivity
      apply ((FlowJetPolynomialDegreeLE.const hc 0).mul
        ((hP i j).mul (hQ (a - i) (b - j)))).mono
      have hi := i.isLt
      have hj := j.isLt
      omega
    have hinner (j : Fin (b + 1)) := flowJetPolynomial_exists_finite_sum
      (R j) (a + b + (rawExprWeight e + rawExprWeight d)) (hR j)
    choose S hS heS using hinner
    obtain ⟨Ptotal, hTotal, heTotal⟩ := flowJetPolynomial_exists_finite_sum
      S (a + b + (rawExprWeight e + rawExprWeight d)) hS
    refine ⟨Ptotal, hTotal, ?_⟩
    intro f hf q X hX hraw
    have hm : mixedDerivative a b
        (fun p => rawExprEval e f p * rawExprEval d f p) q =
        ∑ j : Fin (b + 1), ∑ i : Fin (a + 1),
          (b.choose (j : ℕ) : ℝ) * (a.choose (i : ℕ) : ℝ) *
            mixedDerivative i j (rawExprEval e f) q *
              mixedDerivative (a - i) (b - j) (rawExprEval d f) q := by
      simpa only [Finset.sum_range] using spaces_mixedDerivative_mul
        (contDiff_rawExprEval e hf) (contDiff_rawExprEval d hf) a b q
    change |mixedDerivative a b
      (fun p => rawExprEval e f p * rawExprEval d f p) q| ≤ _
    rw [hm, heTotal X]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [heS j X]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have hc : 0 ≤ (b.choose (j : ℕ) : ℝ) * (a.choose (i : ℕ) : ℝ) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hc]
    simp only [R, flowJetPolynomialEval_mul, flowJetPolynomialEval_const]
    have hmprod := mul_le_mul (hbP i j f hf q X hX hraw)
      (hbQ (a - i) (b - j) f hf q X hX hraw) (abs_nonneg _)
      (flowJetPolynomialEval_nonneg (hP i j) hX)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmprod hc
  | radial e he =>
    obtain ⟨P, hP, hbP⟩ := he (a + 1) b
    refine ⟨P, hP.mono (by simp only [rawExprWeight]; omega), ?_⟩
    intro f hf q X hX hraw
    change |mixedDerivative a b (radialPartial (rawExprEval e f)) q| ≤ _
    rw [mixedDerivative_radialPartial isOpen_univ (contDiff_rawExprEval e hf).contDiffOn
      a b (mem_univ q)]
    exact hbP f hf q X hX hraw
  | angular e he =>
    obtain ⟨P, hP, hbP⟩ := he a (b + 1)
    refine ⟨P, hP.mono (by simp only [rawExprWeight]; omega), ?_⟩
    intro f hf q X hX hraw
    change |mixedDerivative a b (angularPartial (rawExprEval e f)) q| ≤ _
    rw [mixedDerivative_angularPartial isOpen_univ (contDiff_rawExprEval e hf).contDiffOn
      a b (mem_univ q)]
    exact hbP f hf q X hX hraw

private theorem rawExpr_frechet_majorant (e : CanonicalRawExpr) (n : ℕ) :
    ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P (n + rawExprWeight e) ∧
      ∀ f : Fin 9 → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (f i)) →
      ∀ q : PolarPoint, ∀ X : ℕ → ℝ, (∀ k, 0 ≤ X k) →
        (∀ i a b, |mixedDerivative a b (f i) q| ≤ X (a + b)) →
        ‖iteratedFDeriv ℝ n (rawExprEval e f) q‖ ≤ flowJetPolynomialEval P X := by
  classical
  have hpart (i : Fin (n + 1)) := rawExpr_mixed_majorant e i (n - i)
  choose P hP hbP using hpart
  have hPn (i : Fin (n + 1)) : FlowJetPolynomialDegreeLE (P i) (n + rawExprWeight e) := by
    apply (hP i).mono
    have hi := i.isLt
    omega
  obtain ⟨S, hS, heS⟩ := flowJetPolynomial_exists_finite_sum P (n + rawExprWeight e) hPn
  let R : FlowJetPolynomial := flowJetPolynomialMul [((2 : ℝ) ^ n, [])] S
  have hR : FlowJetPolynomialDegreeLE R (n + rawExprWeight e) := by
    simpa only [Nat.zero_add] using
      (FlowJetPolynomialDegreeLE.const (c := (2 : ℝ) ^ n) (by positivity) 0).mul hS
  refine ⟨R, hR, ?_⟩
  intro f hf q X hX hraw
  have hs0 : 0 ≤ flowJetPolynomialEval S X := flowJetPolynomialEval_nonneg hS hX
  have hmix (a b : ℕ) (hab : a + b = n) :
      ‖mixedDerivative a b (rawExprEval e f) q‖ ≤ flowJetPolynomialEval S X := by
    let i : Fin (n + 1) := ⟨a, by omega⟩
    have he : n - (i : ℕ) = b := by dsimp only [i]; omega
    have hb := hbP i f hf q X hX hraw
    rw [he] at hb
    have hsingle : flowJetPolynomialEval (P i) X ≤ flowJetPolynomialEval S X := by
      rw [heS X]
      exact Finset.single_le_sum
        (fun j _ => flowJetPolynomialEval_nonneg (hPn j) hX) (Finset.mem_univ i)
    simpa only [Real.norm_eq_abs] using hb.trans hsingle
  have hb := norm_iteratedFDeriv_le_of_mixedDerivative isOpen_univ
    (contDiff_rawExprEval e hf).contDiffOn n (mem_univ q) hs0 hmix
  simpa only [R, flowJetPolynomialEval_mul, flowJetPolynomialEval_const] using hb

private def rawPotentialExpr : CanonicalRawExpr :=
  .mul (.mul (.atom 7) (.atom 8))
    (.add
      (.radial (.add (.mul (.atom 0) (.radial (.atom 7)))
        (.mul (.atom 1) (.angular (.atom 7)))))
      (.angular (.add (.mul (.atom 1) (.radial (.atom 7)))
        (.mul (.atom 2) (.angular (.atom 7))))))

private def rawDensityBilinear (u v s t : CanonicalRawExpr) : CanonicalRawExpr :=
  .mul (.mul (.mul (.atom 7) (.atom 7)) (.atom 8))
    (.add
      (.add (.mul (.atom 0) (.mul u s))
        (.mul (.atom 1) (.add (.mul u t) (.mul v s))))
      (.mul (.atom 2) (.mul v t)))

private def rawDensityExpr (i : Fin 3) : CanonicalRawExpr :=
  let r₁ := CanonicalRawExpr.atom 3
  let t₁ := CanonicalRawExpr.atom 4
  let r₂ := CanonicalRawExpr.atom 5
  let t₂ := CanonicalRawExpr.atom 6
  if i = 0 then rawDensityBilinear r₁ t₁ r₁ t₁
  else if i = 1 then rawDensityBilinear r₁ t₁ r₂ t₂
  else rawDensityBilinear r₂ t₂ r₂ t₂

private def rawPhysicalFieldExpr : Fin 4 → CanonicalRawExpr :=
  Fin.cases rawPotentialExpr rawDensityExpr

private theorem rawPhysicalFieldExpr_weight (i : Fin 4) :
    rawExprWeight (rawPhysicalFieldExpr i) ≤ 2 := by
  refine Fin.cases ?_ ?_ i
  · change rawExprWeight rawPotentialExpr ≤ 2
    simp [rawPotentialExpr, rawExprWeight]
  · intro j
    change rawExprWeight (rawDensityExpr j) ≤ 2
    fin_cases j <;> simp [rawDensityExpr, rawDensityBilinear, rawExprWeight]

/-- The four scalar entries of the actual chart derivative, ordered
as radial/angle derivatives of the first and then second output. -/
def coordinateChartDerivativeField (F : PolarPoint → PolarPoint) :
    Fin 4 → PolarPoint → ℝ :=
  ![(fun p => (fderiv ℝ F p (1, 0)).1),
    (fun p => (fderiv ℝ F p (0, 1)).1),
    (fun p => (fderiv ℝ F p (1, 0)).2),
    (fun p => (fderiv ℝ F p (0, 1)).2)]

/-- The nine actual primitive scalar fields used in the coordinate
formulas: a, b, c, the four entries of the actual chart derivative,
height, and |J|⁻¹. No zeroth-order angular lift bound is required. -/
def coordinatePrimitiveJetField (A : SymmetricCoefficients)
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) : Fin 9 → PolarPoint → ℝ :=
  ![A.a, A.b, A.c, coordinateChartDerivativeField F 0,
    coordinateChartDerivativeField F 1, coordinateChartDerivativeField F 2,
    coordinateChartDerivativeField F 3, h,
    (fun p => |planeJacobian F p|⁻¹)]

private theorem rawPotentialExpr_eval (A : SymmetricCoefficients)
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) :
    rawExprEval rawPotentialExpr (coordinatePrimitiveJetField A F h) =
      (fun p => h p * divergenceOperator A h p / |planeJacobian F p|) := by
  funext p
  simp [rawPotentialExpr, rawExprEval, coordinatePrimitiveJetField,
    divergenceOperator, div_eq_mul_inv] <;> ring

private theorem rawDensityExpr_eval (A : SymmetricCoefficients)
    (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) (i : Fin 3) :
    rawExprEval (rawDensityExpr i) (coordinatePrimitiveJetField A F h) =
      canonicalCoefficientComponent i (coordinatePrincipalDensity A F h) := by
  funext p
  fin_cases i <;>
    simp [rawDensityExpr, rawDensityBilinear, rawExprEval,
      coordinatePrimitiveJetField, coordinateChartDerivativeField,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      canonicalCoefficientComponent, coordinatePrincipalDensity, coefficientQuadratic,
      div_eq_mul_inv] <;> ring

/-- Smoothness of the actual physical fields follows from the nine
actual primitive fields, independently of the quantitative estimates. -/
theorem contDiff_coordinatePhysicalFields
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ)
    (hfields : ∀ i, ContDiff ℝ ∞ (coordinatePrimitiveJetField A F h i)) :
    ContDiff ℝ ∞ (fun x => h x * divergenceOperator A h x / |planeJacobian F x|) ∧
      ∀ i : Fin 3, ContDiff ℝ ∞
        (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h)) := by
  constructor
  · rw [← rawPotentialExpr_eval A F h]
    exact contDiff_rawExprEval rawPotentialExpr hfields
  · intro i
    rw [← rawDensityExpr_eval A F h i]
    exact contDiff_rawExprEval (rawDensityExpr i) hfields

private theorem rawFieldFamily_fixed_loss_material_bound
    {ι : Type} [Fintype ι] (e : ι → CanonicalRawExpr) (N : ℕ)
    (hweight : ∀ i, rawExprWeight (e i) ≤ N)
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ C : ℕ → ℝ, (∀ k, 1 ≤ C k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ f : Fin 9 → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (f i)) →
      ∀ q : PolarPoint,
        (∀ i a b, |mixedDerivative a b (f i) q| ≤
          C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z)) →
      ∀ n : ℕ, ∀ i : ι, ‖iteratedFDeriv ℝ n (rawExprEval (e i) f) q‖ ≤
        B n * W ^ (B n) * (1 + p (n + loss) z) := by
  classical
  obtain ⟨base, loss, hmaterial⟩ := flowJetPolynomial_le_material_one_high hp hI inputLoss
  have hmajorant (n : ℕ) :
      ∃ P : FlowJetPolynomial, FlowJetPolynomialDegreeLE P (n + N) ∧
        ∀ f : Fin 9 → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (f i)) →
        ∀ q : PolarPoint, ∀ X : ℕ → ℝ, (∀ k, 0 ≤ X k) →
          (∀ i a b, |mixedDerivative a b (f i) q| ≤ X (a + b)) →
          ∀ i : ι, ‖iteratedFDeriv ℝ n (rawExprEval (e i) f) q‖ ≤
            flowJetPolynomialEval P X := by
    have hi (i : ι) := rawExpr_frechet_majorant (e i) n
    choose Q hQ hbQ using hi
    have hQn (i : ι) : FlowJetPolynomialDegreeLE (Q i) (n + N) :=
      (hQ i).mono (Nat.add_le_add_left (hweight i) n)
    obtain ⟨P, hP, heP⟩ := flowJetPolynomial_exists_finite_sum Q (n + N) hQn
    refine ⟨P, hP, ?_⟩
    intro f hf q X hX hraw i
    apply (hbQ i f hf q X hX hraw).trans
    rw [heP X]
    exact Finset.single_le_sum (fun j _ => flowJetPolynomialEval_nonneg (hQn j) hX)
      (Finset.mem_univ i)
  choose P hP hbP using hmajorant
  refine ⟨base, N + loss, ?_⟩
  intro C hC
  have hc (n : ℕ) := hmaterial (n + N) (P n) (hP n) C hC
  choose B hB hb using hc
  refine ⟨B, hB, ?_⟩
  intro z hz W hW f hf q hraw n i
  let X : ℕ → ℝ := fun k => C k * W ^ (C k) * (1 + p (k + inputLoss) z)
  have hX (k : ℕ) : 0 ≤ X k :=
    mul_nonneg (mul_nonneg (zero_le_one.trans (hC k))
      (Real.rpow_nonneg (zero_le_one.trans hW) _))
      (add_nonneg zero_le_one (apply_nonneg _ _))
  have he := (hbP n f hf q X hX hraw i).trans (hb n z hz W hW)
  simpa only [Nat.add_assoc] using he

/-- One low order and one fixed loss bound the actual physical potential
and every actual principal-density component. Constants are chosen before
the state, envelope, fields, point, and requested derivative order. -/
theorem coordinatePhysicalFields_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ C : ℕ → ℝ, (∀ k, 1 ≤ C k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ A : SymmetricCoefficients, ∀ F : PolarPoint → PolarPoint,
      ∀ h : PolarPoint → ℝ,
        (∀ i, ContDiff ℝ ∞ (coordinatePrimitiveJetField A F h i)) →
      ∀ q : PolarPoint,
        (∀ i a b, |mixedDerivative a b (coordinatePrimitiveJetField A F h i) q| ≤
          C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z)) →
      ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n
          (fun x => h x * divergenceOperator A h x / |planeJacobian F x|) q‖ ≤
            B n * W ^ (B n) * (1 + p (n + loss) z) ∧
        ∀ i : Fin 3,
          ‖iteratedFDeriv ℝ n (canonicalCoefficientComponent i
            (coordinatePrincipalDensity A F h)) q‖ ≤
              B n * W ^ (B n) * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hbound⟩ := rawFieldFamily_fixed_loss_material_bound
    rawPhysicalFieldExpr 2 rawPhysicalFieldExpr_weight hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro C hC
  obtain ⟨B, hB, hb⟩ := hbound C hC
  refine ⟨B, hB, ?_⟩
  intro z hz W hW A F h hfields q hraw n
  have hout := hb z hz W hW (coordinatePrimitiveJetField A F h) hfields q hraw n
  constructor
  · have ho := hout 0
    change ‖iteratedFDeriv ℝ n
      (rawExprEval rawPotentialExpr (coordinatePrimitiveJetField A F h)) q‖ ≤ _ at ho
    rw [rawPotentialExpr_eval] at ho
    exact ho
  · intro i
    have ho := hout i.succ
    change ‖iteratedFDeriv ℝ n
      (rawExprEval (rawDensityExpr i) (coordinatePrimitiveJetField A F h)) q‖ ≤ _ at ho
    rw [rawDensityExpr_eval A F h i] at ho
    exact ho

/-- Actual smoothness on an explicit open domain is sufficient for the
physical fields. No common infinite-order neighborhood is inferred from
smoothness only at a boundary point. -/
theorem contDiffOn_coordinatePhysicalFields
    {U : Set PolarPoint} (hU : IsOpen U)
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ)
    (hfields : ∀ i, ContDiffOn ℝ ∞ (coordinatePrimitiveJetField A F h i) U) :
    ContDiffOn ℝ ∞ (fun x => h x * divergenceOperator A h x / |planeJacobian F x|) U ∧
      ∀ i : Fin 3, ContDiffOn ℝ ∞
        (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h)) U := by
  constructor
  · intro q hq
    have hs := contDiffAt_rawExprEval rawPotentialExpr
      (fun i => (hfields i).contDiffAt (hU.mem_nhds hq))
    rw [rawPotentialExpr_eval A F h] at hs
    exact hs.contDiffWithinAt
  · intro i q hq
    have hs := contDiffAt_rawExprEval (rawDensityExpr i)
      (fun j => (hfields j).contDiffAt (hU.mem_nhds hq))
    rw [rawDensityExpr_eval A F h i] at hs
    exact hs.contDiffWithinAt

/-- The same constants control actual fields on any explicit open domain.
A genuine global representative is used only to apply the existing
Leibniz formula; all of its input and output jets equal the actual jets. -/
theorem coordinatePhysicalFieldsOn_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ C : ℕ → ℝ, (∀ k, 1 ≤ C k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ A : SymmetricCoefficients, ∀ F : PolarPoint → PolarPoint,
      ∀ h : PolarPoint → ℝ, ∀ U : Set PolarPoint, IsOpen U →
        (∀ i, ContDiffOn ℝ ∞ (coordinatePrimitiveJetField A F h i) U) →
      ∀ q ∈ U,
        (∀ i a b, |mixedDerivative a b (coordinatePrimitiveJetField A F h i) q| ≤
          C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z)) →
      ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n
          (fun x => h x * divergenceOperator A h x / |planeJacobian F x|) q‖ ≤
            B n * W ^ (B n) * (1 + p (n + loss) z) ∧
        ∀ i : Fin 3,
          ‖iteratedFDeriv ℝ n (canonicalCoefficientComponent i
            (coordinatePrincipalDensity A F h)) q‖ ≤
              B n * W ^ (B n) * (1 + p (n + loss) z) := by
  classical
  obtain ⟨base, loss, hbound⟩ := rawFieldFamily_fixed_loss_material_bound
    rawPhysicalFieldExpr 2 rawPhysicalFieldExpr_weight hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro C hC
  obtain ⟨B, hB, hb⟩ := hbound C hC
  refine ⟨B, hB, ?_⟩
  intro z hz W hW A F h U hU hfields q hq hraw n
  have hrep (i : Fin 9) := exists_global_contDiff_germ_of_open hU (hfields i) hq
  choose f hf he using hrep
  have hrawf (i : Fin 9) (a b : ℕ) : |mixedDerivative a b (f i) q| ≤
      C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z) :=
    (congrArg abs (mixedDerivative_eq_of_germ (he i) a b)).trans_le (hraw i a b)
  have hout (i : Fin 4) :
      ‖iteratedFDeriv ℝ n
        (rawExprEval (rawPhysicalFieldExpr i) (coordinatePrimitiveJetField A F h)) q‖ ≤
          B n * W ^ (B n) * (1 + p (n + loss) z) := by
    have hgerm := rawExprEval_eventuallyEq (rawPhysicalFieldExpr i) he
    rw [← (hgerm.iteratedFDeriv ℝ n).self_of_nhds]
    exact hb z hz W hW f hf q hrawf n i
  constructor
  · have ho := hout 0
    change ‖iteratedFDeriv ℝ n
      (rawExprEval rawPotentialExpr (coordinatePrimitiveJetField A F h)) q‖ ≤ _ at ho
    rw [rawPotentialExpr_eval] at ho
    exact ho
  · intro i
    have ho := hout i.succ
    change ‖iteratedFDeriv ℝ n
      (rawExprEval (rawDensityExpr i) (coordinatePrimitiveJetField A F h)) q‖ ≤ _ at ho
    rw [rawDensityExpr_eval A F h i] at ho
    exact ho

/-- Smooth actual derivative entries give a smooth actual determinant
on the same explicit open domain. -/
theorem contDiffOn_planeJacobian_of_chartDerivativeFields
    {U : Set PolarPoint} (F : PolarPoint → PolarPoint)
    (hfields : ∀ i, ContDiffOn ℝ ∞ (coordinateChartDerivativeField F i) U) :
    ContDiffOn ℝ ∞ (planeJacobian F) U := by
  have he : planeJacobian F =
      (fun q => coordinateChartDerivativeField F 0 q * coordinateChartDerivativeField F 3 q -
        coordinateChartDerivativeField F 2 q * coordinateChartDerivativeField F 1 q) := by
    funext q
    simp [planeJacobian, coordinateChartDerivativeField]
  rw [he]
  exact ((hfields 0).mul (hfields 3)).sub ((hfields 2).mul (hfields 1))

private def rawJacobianProduct (side : Bool) : CanonicalRawExpr :=
  if side then .mul (.atom 5) (.atom 4) else .mul (.atom 3) (.atom 6)

/-- The actual Jacobian is the difference of two products of genuine
first chart derivatives. Its bound uses only those four fields and
does not assume any reciprocal-Jacobian estimate. -/
theorem coordinateJacobianOn_fixed_loss_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ C : ℕ → ℝ, (∀ k, 1 ≤ C k) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ F : PolarPoint → PolarPoint, ∀ U : Set PolarPoint, IsOpen U →
        (∀ i, ContDiffOn ℝ ∞ (coordinateChartDerivativeField F i) U) →
      ∀ q ∈ U,
        (∀ i a b, |mixedDerivative a b (coordinateChartDerivativeField F i) q| ≤
          C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z)) →
      ∀ n : ℕ, ‖iteratedFDeriv ℝ n (planeJacobian F) q‖ ≤
        B n * W ^ (B n) * (1 + p (n + loss) z) := by
  classical
  have hweight (side : Bool) : rawExprWeight (rawJacobianProduct side) ≤ 0 := by
    cases side <;> simp [rawJacobianProduct, rawExprWeight]
  obtain ⟨base, loss, hbound⟩ := rawFieldFamily_fixed_loss_material_bound
    rawJacobianProduct 0 hweight hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro C hC
  obtain ⟨B, hB, hb⟩ := hbound C hC
  let D : ℕ → ℝ := fun n => 1 + 2 * B n
  have hD (n : ℕ) : 0 < D n := by
    dsimp only [D]
    linarith [hB n]
  refine ⟨D, hD, ?_⟩
  intro z hz W hW F U hU hfields q hq hraw n
  have hrep (i : Fin 4) := exists_global_contDiff_germ_of_open hU (hfields i) hq
  choose g hg he using hrep
  let f : Fin 9 → PolarPoint → ℝ := fun i =>
    if i = 3 then g 0 else if i = 4 then g 1 else
      if i = 5 then g 2 else if i = 6 then g 3 else fun _ => 0
  have hf (i : Fin 9) : ContDiff ℝ ∞ (f i) := by
    dsimp only [f]
    split_ifs
    · exact hg 0
    · exact hg 1
    · exact hg 2
    · exact hg 3
    · exact contDiff_const
  have hrawg (i : Fin 4) (a b : ℕ) : |mixedDerivative a b (g i) q| ≤
      C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z) :=
    (congrArg abs (mixedDerivative_eq_of_germ (he i) a b)).trans_le (hraw i a b)
  have hzero (a b : ℕ) : |mixedDerivative a b (fun _ : PolarPoint => (0 : ℝ)) q| = 0 := by
    simp [mixedDerivative, iteratedDeriv_const]
  have hrawf (i : Fin 9) (a b : ℕ) : |mixedDerivative a b (f i) q| ≤
      C (a + b) * W ^ (C (a + b)) * (1 + p (a + b + inputLoss) z) := by
    dsimp only [f]
    split_ifs
    · exact hrawg 0 a b
    · exact hrawg 1 a b
    · exact hrawg 2 a b
    · exact hrawg 3 a b
    · rw [hzero]
      exact mul_nonneg (mul_nonneg (zero_le_one.trans (hC (a + b)))
        (Real.rpow_nonneg (zero_le_one.trans hW) _))
        (add_nonneg zero_le_one (apply_nonneg _ _))
  let L : PolarPoint → ℝ := fun y => g 0 y * g 3 y
  let R : PolarPoint → ℝ := fun y => g 2 y * g 1 y
  have hL : ContDiff ℝ ∞ L := (hg 0).mul (hg 3)
  have hR : ContDiff ℝ ∞ R := (hg 2).mul (hg 1)
  have hleft : rawExprEval (rawJacobianProduct false) f = L := by
    funext y
    simp [rawJacobianProduct, rawExprEval, f, L]
  have hright : rawExprEval (rawJacobianProduct true) f = R := by
    funext y
    simp [rawJacobianProduct, rawExprEval, f, R]
  have hLb := hb z hz W hW f hf q hrawf n false
  have hRb := hb z hz W hW f hf q hrawf n true
  rw [hleft] at hLb
  rw [hright] at hRb
  have hdet : L - R =ᶠ[𝓝 q] planeJacobian F := by
    filter_upwards [he 0, he 1, he 2, he 3] with y h₀ h₁ h₂ h₃
    simp [Pi.sub_apply, L, R, h₀, h₁, h₂, h₃, coordinateChartDerivativeField,
      planeJacobian]
  have htwice : ‖iteratedFDeriv ℝ n (planeJacobian F) q‖ ≤
      (2 * B n) * W ^ (B n) * (1 + p (n + loss) z) := by
    rw [← (hdet.iteratedFDeriv ℝ n).self_of_nhds,
      iteratedFDeriv_sub_apply (hL.contDiffAt.of_le (by simp))
        (hR.contDiffAt.of_le (by simp))]
    have hs := (norm_sub_le _ _).trans (add_le_add hLb hRb)
    nlinarith only [hs]
  have hcoeff : 2 * B n ≤ D n := by dsimp only [D]; linarith
  have hexp : B n ≤ D n := by dsimp only [D]; linarith [hB n]
  exact htwice.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hcoeff (Real.rpow_le_rpow_of_exponent_le hW hexp)
      (Real.rpow_nonneg (zero_le_one.trans hW) _) (hD n).le)
    (add_nonneg zero_le_one (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis
