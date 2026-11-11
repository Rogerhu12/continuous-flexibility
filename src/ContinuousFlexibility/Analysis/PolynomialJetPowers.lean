import ContinuousFlexibility.Analysis.PolynomialJetComposition
import ContinuousFlexibility.Analysis.ScalarRpowJetGrowth

/-!
# Powers of positive fields with component-power jet bounds

The derivative formula for a real power and the composition estimate
give fixed-power bounds for all Fréchet jets of a positive scalar field.
The lower bound is quantitative; no compactness constant depending on
an individual component is introduced.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem norm_iteratedFDeriv_rpow_polynomial_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    {λ P : ℝ} (hλ : 0 < λ) (hP : 0 ≤ P)
    (hlower : ∀ i x, x ∈ U i → λ * W i ^ (-P) ≤ f i x)
    (hbound : ∀ k : ℕ, ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ Q)
    (r : ℝ) (n : ℕ) :
    ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => f i y ^ r) x‖ ≤ A * W i ^ Q := by
  obtain ⟨A₀, Q₀, hA₀, hQ₀, hzero⟩ := hbound 0
  have hpos (i : ι) (x : E) (hx : x ∈ U i) : 0 < f i x :=
    (mul_pos hλ (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW i)) _)).trans_le
      (hlower i x hx)
  have hupper (i : ι) (x : E) (hx : x ∈ U i) : f i x ≤ A₀ * W i ^ Q₀ := by
    have hb : |f i x| ≤ A₀ * W i ^ Q₀ := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hzero i x hx
    exact (le_abs_self _).trans hb
  have hpow : ContDiffOn ℝ ∞ (fun t : ℝ => t ^ r) (Ioi (0 : ℝ)) :=
    fun x hx => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  apply norm_iteratedFDeriv_comp_polynomial_bound W hW U (fun _ => Ioi (0 : ℝ))
    hU (fun _ => isOpen_Ioi) f (fun _ => fun t : ℝ => t ^ r) hf (fun _ => hpow)
    (fun i x hx => hpos i x hx) n
  · intro k _
    obtain ⟨A, Q, hA, hQ, hb⟩ := iteratedDeriv_rpow_polynomial_bound hλ hA₀ hP hQ₀ r k
    refine ⟨A, Q, hA, hQ, fun i x hx => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hb (W i) (f i x) (hW i) (hlower i x hx) (hupper i x hx)
  · exact fun k _ _ => hbound k

theorem norm_iteratedFDeriv_inv_polynomial_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    {λ P : ℝ} (hλ : 0 < λ) (hP : 0 ≤ P)
    (hlower : ∀ i x, x ∈ U i → λ * W i ^ (-P) ≤ f i x)
    (hbound : ∀ k : ℕ, ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ Q)
    (n : ℕ) :
    ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => (f i y)⁻¹) x‖ ≤ A * W i ^ Q := by
  simpa only [Real.rpow_neg_one] using
    norm_iteratedFDeriv_rpow_polynomial_bound W hW U hU f hf hλ hP hlower hbound (-1 : ℝ) n

theorem norm_iteratedFDeriv_sqrt_polynomial_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    {λ P : ℝ} (hλ : 0 < λ) (hP : 0 ≤ P)
    (hlower : ∀ i x, x ∈ U i → λ * W i ^ (-P) ≤ f i x)
    (hbound : ∀ k : ℕ, ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ Q)
    (n : ℕ) :
    ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => Real.sqrt (f i y)) x‖ ≤ A * W i ^ Q := by
  simpa only [Real.sqrt_eq_rpow] using
    norm_iteratedFDeriv_rpow_polynomial_bound W hW U hU f hf hλ hP hlower hbound (1 / 2 : ℝ) n

end ContinuousFlexibility.Analysis
