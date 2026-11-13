import ContinuousFlexibility.Analysis.PositiveCutoffAllOrderJets
import ContinuousFlexibility.Analysis.PositiveReferenceValueEnvelope
import ContinuousFlexibility.Analysis.LogPolynomialEnvelope
import ContinuousFlexibility.Analysis.ExpPolynomialEnvelope

/-!
# All orders of the same positive reference height

The logarithmic interpolation uses the supplied fixed cutoff width.
Its exponent has polynomial jets, while the exponential amplitude is
bounded by the actual endpoint values. The reciprocal is handled by
the same argument with the exponent negated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- The coefficient is fixed before the width and endpoint functions.
No exponential of a polynomial derivative bound is used. -/
theorem exists_positiveReferenceHeight_allOrder_jet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {l r δ U : ℝ},
      0 < δ → 1 ≤ U → δ⁻¹ ≤ U →
      ∀ h : Bool → ℝ → ℝ,
        (∀ (side : Bool) x, x ∈ Metric.ball (if side then r else l) δ →
          ContDiffAt ℝ ∞ (h side) x) →
        (∀ (side : Bool) x, x ∈ Metric.ball (if side then r else l) δ →
          0 < h side x ∧ h side x ≤ U ∧ (h side x)⁻¹ ≤ U) →
        (∀ (side : Bool) k, k ≤ N →
          ∀ x ∈ Metric.ball (if side then r else l) δ,
            |iteratedDeriv k (h side) x| ≤ U) →
        ∀ k, k ≤ N → ∀ x : ℝ,
          |iteratedDeriv k (positiveReferenceHeight l r δ (h false) (h true)) x| ≤
              C * U ^ ((3 * N + 1) * N + 2) ∧
            |iteratedDeriv k
              (fun t => (positiveReferenceHeight l r δ (h false) (h true) t)⁻¹) x| ≤
              C * U ^ ((3 * N + 1) * N + 2) := by
  obtain ⟨Ccut, hCcut, hcut⟩ := exists_positiveEndpointCutoff_mul_jet_envelope N
  obtain ⟨Clog, hClog, hlog⟩ := exists_log_finiteJet_polynomial_envelope (E := ℝ) N
  obtain ⟨Cexp, hCexp, hexp⟩ := exists_exp_finiteJet_polynomial_envelope (E := ℝ) N
  let D : ℝ := 2 * (Ccut * Clog)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le (by norm_num)
    (one_le_mul_of_one_le_of_one_le hCcut hClog)
  refine ⟨Cexp * D ^ N, one_le_mul_of_one_le_of_one_le hCexp (one_le_pow₀ hD), ?_⟩
  intro l r δ U hδ hU hδU h hsmooth hvalue hjets
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hlogSmooth (side : Bool) :
      ∀ x ∈ Metric.ball (if side then r else l) δ,
        ContDiffAt ℝ ∞ (fun t => Real.log (h side t)) x :=
    fun x hx => (hsmooth side x hx).log (hvalue side x hx).1.ne'
  have hlogJets (side : Bool) (k : ℕ) (hk : k ≤ N)
      (x : ℝ) (hx : x ∈ Metric.ball (if side then r else l) δ) :
      |iteratedDeriv k (fun t => Real.log (h side t)) x| ≤ Clog * U ^ (2 * N + 1) := by
    have hb := hlog hU (h side) x (hsmooth side x hx)
      (hvalue side x hx).1 (hvalue side x hx).2.1 (hvalue side x hx).2.2
      (fun j _ hj => by
        simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
          hjets side j hj x hx) k hk
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb
  have hM : 0 ≤ Clog * U ^ (2 * N + 1) :=
    mul_nonneg (zero_le_one.trans hClog) (pow_nonneg hU0 _)
  have hclipped (side : Bool) (k : ℕ) (hk : k ≤ N) (x : ℝ) :
      |iteratedDeriv k (fun t => positiveEndpointCutoff (if side then r else l) δ t *
        Real.log (h side t)) x| ≤ Ccut * U ^ N * (Clog * U ^ (2 * N + 1)) :=
    hcut hδ hU hδU hM _ _ (hlogSmooth side) (hlogJets side) k hk x
  let e : ℝ → ℝ := fun t => positiveEndpointCutoff l δ t * Real.log (h false t) +
    positiveEndpointCutoff r δ t * Real.log (h true t)
  have he : ContDiff ℝ ∞ e :=
    (contDiff_positiveEndpointCutoff_mul hδ (hlogSmooth false)).add
      (contDiff_positiveEndpointCutoff_mul hδ (hlogSmooth true))
  have hejet (k : ℕ) (hk : k ≤ N) (x : ℝ) :
      |iteratedDeriv k e x| ≤ D * U ^ (3 * N + 1) := by
    change |iteratedDeriv k (fun t =>
      positiveEndpointCutoff l δ t * Real.log (h false t) +
      positiveEndpointCutoff r δ t * Real.log (h true t)) x| ≤ _
    rw [iteratedDeriv_fun_add
      ((contDiff_positiveEndpointCutoff_mul hδ (hlogSmooth false)).contDiffAt.of_le (by simp))
      ((contDiff_positiveEndpointCutoff_mul hδ (hlogSmooth true)).contDiffAt.of_le (by simp))]
    calc
      _ ≤ _ + _ := abs_add_le _ _
      _ ≤ Ccut * U ^ N * (Clog * U ^ (2 * N + 1)) +
          Ccut * U ^ N * (Clog * U ^ (2 * N + 1)) :=
        add_le_add (hclipped false k hk x) (hclipped true k hk x)
      _ = D * U ^ (3 * N + 1) := by
        dsimp only [D]
        rw [show 3 * N + 1 = N + (2 * N + 1) by omega, pow_add]
        ring
  have hJ : 1 ≤ D * U ^ (3 * N + 1) :=
    one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hU)
  have hsigned (reciprocal : Bool) (k : ℕ) (hk : k ≤ N) (x : ℝ) :
      |iteratedDeriv k
        (fun t => Real.exp (if reciprocal then -e t else e t)) x| ≤
        (Cexp * D ^ N) * U ^ ((3 * N + 1) * N + 2) := by
    have hf : ContDiff ℝ ∞ (fun t => if reciprocal then -e t else e t) := by
      cases reciprocal
      · exact he
      · exact he.neg
    have hvalues : Real.exp (e x) ≤ U ^ 2 ∧ (Real.exp (e x))⁻¹ ≤ U ^ 2 :=
      positiveReferenceHeight_value_bounds (l := l) (r := r) (h := h) hδ hU
        (fun side t ht => (hvalue side t ht).1)
        (fun side t ht => (hvalue side t ht).2.1)
        (fun side t ht => (hvalue side t ht).2.2) x
    have hval : Real.exp (if reciprocal then -e x else e x) ≤ U ^ 2 := by
      cases reciprocal
      · exact hvalues.1
      · change Real.exp (-e x) ≤ U ^ 2
        rw [Real.exp_neg]
        exact hvalues.2
    have hraw (j : ℕ) (_hj : 1 ≤ j) (hj : j ≤ N) :
        ‖iteratedFDeriv ℝ j (fun t => if reciprocal then -e t else e t) x‖ ≤
          D * U ^ (3 * N + 1) := by
      cases reciprocal <;>
        simpa only [Bool.false_eq_true, ite_false, ite_true,
          norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
          iteratedDeriv_fun_neg, abs_neg] using hejet j hj x
    have hb := hexp hJ (sq_nonneg U)
      (fun t : ℝ => if reciprocal then -e t else e t) x hf.contDiffAt hval hraw k hk
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
    have hpower : U ^ 2 * (U ^ (3 * N + 1)) ^ N =
        U ^ ((3 * N + 1) * N + 2) := by
      calc
        _ = U ^ ((3 * N + 1) * N) * U ^ 2 := by
          rw [pow_mul U (3 * N + 1) N]
          ring
        _ = _ := (pow_add U ((3 * N + 1) * N) 2).symm
    calc
      _ ≤ Cexp * U ^ 2 * (D * U ^ (3 * N + 1)) ^ N := hb
      _ = (Cexp * D ^ N) * (U ^ 2 * (U ^ (3 * N + 1)) ^ N) := by
        rw [mul_pow]
        ring
      _ = _ := by rw [hpower]
  intro k hk x
  change |iteratedDeriv k (fun t => Real.exp (e t)) x| ≤ _ ∧
    |iteratedDeriv k (fun t => (Real.exp (e t))⁻¹) x| ≤ _
  constructor
  · exact hsigned false k hk x
  · have hb : |iteratedDeriv k (fun t => Real.exp (-e t)) x| ≤
        (Cexp * D ^ N) * U ^ ((3 * N + 1) * N + 2) := hsigned true k hk x
    simpa only [Real.exp_neg] using hb

end ContinuousFlexibility.Analysis
