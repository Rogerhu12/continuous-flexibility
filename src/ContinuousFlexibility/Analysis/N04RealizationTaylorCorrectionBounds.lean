module

public import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightTaylorJets
public import ContinuousFlexibility.Analysis.N06BoundaryPatchBounds
public import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus

/-!
# The fixed Taylor correction as an actual parameter-linear operator

The existing endpoint cutoffs and Taylor monomials are independent of
the state. Their exact separated mixed derivative formula turns each
parameter jet into a finite linear combination of the supplied angular
trace jets. The compiled uniform radial-factor bound displays the full
inverse-width cost and introduces no new parameter loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04Realization_endpointTaylorCorrection_mixed_formula
    (n : ℕ) (l r δ : ℝ) (A : Bool → ℕ → ℝ → ℝ)
    (hA : ∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j))
    (a b : ℕ) (q : PolarPoint) :
    mixedDerivative a b (endpointTaylorCorrection n l r δ A) q =
      ∑ i : Bool × Fin (n + 1),
        iteratedDeriv a (fun t => positiveEndpointCutoff (if i.1 then r else l) δ t *
          ((t - (if i.1 then r else l)) ^ i.2.val / (i.2.val.factorial : ℝ))) q.1 *
        iteratedDeriv b (A i.1 i.2.val) q.2 := by
  classical
  let e : Bool → ℝ := fun side => if side then r else l
  let w : Bool × Fin (n + 1) → ℝ → ℝ := fun i t =>
    positiveEndpointCutoff (e i.1) δ t * ((t - e i.1) ^ i.2.val / (i.2.val.factorial : ℝ))
  have hw (i : Bool × Fin (n + 1)) : ContDiff ℝ ∞ (w i) :=
    (contDiff_positiveEndpointCutoff (e i.1) δ).mul
      (((contDiff_id.sub contDiff_const).pow i.2.val).div_const _)
  have heq : endpointTaylorCorrection n l r δ A =
      (fun p => ∑ i : Bool × Fin (n + 1), w i p.1 * A i.1 i.2.val p.2) := by
    funext p
    have hterm (side : Bool) :
        (∑ j : Fin (n + 1), w (side, j) p.1 * A side j.val p.2) =
          positiveEndpointCutoff (e side) δ p.1 * boundaryTaylorPolynomial n (e side) (A side) p := by
      rw [Fin.sum_univ_eq_sum_range (fun j =>
        (positiveEndpointCutoff (e side) δ p.1 *
          ((p.1 - e side) ^ j / (j.factorial : ℝ))) * A side j p.2)]
      unfold boundaryTaylorPolynomial
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [Fintype.sum_prod_type]
    simp_rw [hterm]
    simp [endpointTaylorCorrection, e, add_comm]
  rw [heq]
  rw [n07a_mixedDerivative_sum_on isOpen_univ
    (I := Finset.univ)
    (f := fun (i : Bool × Fin (n + 1)) (p : PolarPoint) =>
      w i p.1 * A i.1 i.2.val p.2)
    (fun i _ => by
      simpa only [Function.comp_apply] using
        (((hw i).comp contDiff_fst).mul
          ((hA i.1 i.2.val (Nat.le_of_lt_succ i.2.isLt)).comp contDiff_snd)).contDiffOn)
    a b (mem_univ q)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mixedDerivative, iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field,
    w, e]

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The same constant works at every parameter order because the fixed
Taylor correction is linear in the actual endpoint traces. -/
theorem n04Realization_endpointTaylorCorrection_parameter_bound (n s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : Set X), IsOpen U →
      ∀ A : X → Bool → ℕ → ℝ → ℝ,
      (∀ x ∈ U, ∀ side j, j ≤ n → ContDiff ℝ ∞ (A x side j)) →
      ∀ JA : ∀ side, ∀ j : ℕ, j ≤ n → ∀ b θ,
        SmoothDirections U (fun x => iteratedDeriv b (A x side j) θ),
      ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ k a b : ℕ, a + b ≤ s →
      ∀ q : PolarPoint, ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (endpointTaylorCorrection n l r δ (A x)) q),
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ M H t : ℝ, 0 ≤ M → 0 ≤ H → 1 ≤ t →
      (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n,
        ‖(JA side j hj b q.2).D k x v‖ ≤ M * parameterHeightWeight H k * t ^ b) →
      ‖J.D k x v‖ ≤ C * δ⁻¹ ^ s * M * parameterHeightWeight H k * t ^ (a + b) := by
  classical
  obtain ⟨Cr, hCr, hrad⟩ := n06_boundaryTaylor_radial_factor_bound n s
  let I : Type := Bool × Fin (n + 1)
  let C : ℝ := 1 + (Fintype.card I : ℝ) * Cr
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hCr))
  refine ⟨C, hC, ?_⟩
  intro U hU A hA JA l r δ hδ hδ1 k a b hab q J x hx v M H t hM hH ht hraw
  let coeff : I → ℝ := fun i => iteratedDeriv a
    (fun z => positiveEndpointCutoff (if i.1 then r else l) δ z *
      ((z - (if i.1 then r else l)) ^ i.2.val / (i.2.val.factorial : ℝ))) q.1
  let JT : ∀ i : I, SmoothDirections U (fun y => iteratedDeriv b (A y i.1 i.2.val) q.2) :=
    fun i => JA i.1 i.2.val (Nat.le_of_lt_succ i.2.isLt) b q.2
  have hd := smoothDirections_D_eq_linearCombination J JT coeff
    (fun y hy => n04Realization_endpointTaylorCorrection_mixed_formula
      n l r δ (A y) (hA y hy) a b q) k hx v
  let W : ℝ := δ⁻¹ ^ s * M * parameterHeightWeight H k * t ^ (a + b)
  have hW : 0 ≤ W := mul_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hδ.le) _) hM)
      (parameterHeightWeight_nonneg hH k)) (pow_nonneg (zero_le_one.trans ht) _)
  have hterm (i : I) : ‖coeff i * (JT i).D k x v‖ ≤ Cr * W := by
    have hc : |coeff i| ≤ Cr * δ⁻¹ ^ s := hrad i.2.val
      (Nat.le_of_lt_succ i.2.isLt) a (by omega) (if i.1 then r else l) δ q.1 hδ hδ1
    have hj : ‖(JT i).D k x v‖ ≤ M * parameterHeightWeight H k * t ^ (a + b) :=
      (hraw i.1 i.2.val (Nat.le_of_lt_succ i.2.isLt)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega))
          (mul_nonneg hM (parameterHeightWeight_nonneg hH k)))
    calc
      _ = |coeff i| * ‖(JT i).D k x v‖ := by rw [norm_mul, Real.norm_eq_abs]
      _ ≤ (Cr * δ⁻¹ ^ s) * (M * parameterHeightWeight H k * t ^ (a + b)) :=
        mul_le_mul hc hj (norm_nonneg _) (by positivity)
      _ = Cr * W := by dsimp only [W]; ring
  rw [hd]
  calc
    _ ≤ ∑ i : I, ‖coeff i * (JT i).D k x v‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, Cr * W := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((Fintype.card I : ℝ) * Cr) * W := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ C * W := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hW
    _ = _ := by dsimp only [W]; ring

end ContinuousFlexibility.Analysis
