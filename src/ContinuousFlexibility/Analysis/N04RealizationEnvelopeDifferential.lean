import ContinuousFlexibility.Analysis.N04RealizationEnvelopeComposition

/-!
# Differential operations on finite envelopes

All bounds use the same index set and coefficient weight. Taking the
actual derivative shifts the input order by one; square root uses its
positive value and reciprocal value, without a second representation of
the square-root field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

variable {X D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem n04Realization_envelope_clm_comp_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (L : X → E →L[ℝ] F) (f : X → D → E)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (p x)) (n : ℕ)
    (hL : HasPositiveEnvelope W (fun x => ‖L x‖))
    (hfj : HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n (f x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (L x ∘ f x) (p x)‖) := by
  exact (hL.mul hW hfj (fun _ => norm_nonneg _)).mono (fun x =>
    (L x).norm_iteratedFDeriv_comp_left (hf x) (by simp : (n : ℕ∞ω) ≤ ∞))

theorem n04Realization_envelope_fderiv_jets
    {W : X → ℝ} (p : X → D) (f : X → D → E) (n : ℕ)
    (hf : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ (n + 1) (f x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fderiv ℝ (f x)) (p x)‖) := by
  simpa only [norm_iteratedFDeriv_fderiv] using hf

theorem n04Realization_envelope_directional_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (f : X → D → E) (v : X → D)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (p x)) (n : ℕ)
    (hv : HasPositiveEnvelope W (fun x => ‖v x‖))
    (hfj : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ (n + 1) (f x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ (f x) y (v x)) (p x)‖) := by
  apply (hv.mul hW hfj (fun _ => norm_nonneg _)).mono
  intro x
  have h := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ (f x)) (c := v x) (x := p x) (n := n)
    ((hf x).fderiv_right (m := ∞) (by simp)) (by simp)
  simpa only [norm_iteratedFDeriv_fderiv] using h

theorem n04Realization_envelope_add_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (f g : X → D → E)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (p x))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x)) (n : ℕ)
    (hfj : HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n (f x) (p x)‖))
    (hgj : HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n (g x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fun y => f x y + g x y) (p x)‖) := by
  apply (hfj.add hW hgj).mono
  intro x
  have h := norm_add_le (iteratedFDeriv ℝ n (f x) (p x))
    (iteratedFDeriv ℝ n (g x) (p x))
  rw [← iteratedFDeriv_add_apply
    ((hf x).of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    ((hg x).of_le (by simp : (n : ℕ∞ω) ≤ ∞))] at h
  have heq : f x + g x = (fun y => f x y + g x y) :=
    funext (fun y => Pi.add_apply (f x) (g x) y)
  rw [heq] at h
  exact h

theorem n04Realization_norm_iteratedFDeriv_sqrt_le
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ‖iteratedFDeriv ℝ n Real.sqrt t‖ ≤
      |rpowJetCoefficient (1 / 2) n| * Real.sqrt t * (t⁻¹) ^ n := by
  have h := endpoint_rpowJet_bound (q := t) (δ := 1) (c := t) (M := t)
    zero_lt_one ht ht.le (by simp) (by simp) 0 n
  have hsqrt : Real.sqrt = (fun y : ℝ => y ^ (1 / 2 : ℝ)) := by
    funext y
    exact Real.sqrt_eq_rpow y
  rw [hsqrt, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  simpa only [Real.sqrt_eq_rpow, Nat.cast_zero, sub_zero, zero_add, one_pow,
    one_mul, Real.one_rpow, mul_one, div_eq_mul_inv, inv_pow, mul_assoc] using h

/-- Only the reciprocal value is needed for all outer square-root jets. -/
theorem n04Realization_envelope_sqrt_outer_jets
    {W t : X → ℝ} (hW : ∀ x, 1 ≤ W x) (ht : ∀ x, 0 < t x)
    (hval : HasPositiveEnvelope W t)
    (hinv : HasPositiveEnvelope W (fun x => (t x)⁻¹)) (n : ℕ) :
    HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n Real.sqrt (t x)‖) := by
  have hs := hval.sqrt hW (fun x => (ht x).le)
  have hi := hinv.pow hW (fun x => (inv_pos.mpr (ht x)).le) n
  have hc := (hasPositiveEnvelope_const W hW |rpowJetCoefficient (1 / 2) n|).mul
    hW hs (fun _ => Real.sqrt_nonneg _)
  exact (hc.mul hW hi (fun x => pow_nonneg (inv_pos.mpr (ht x)).le n)).mono
    (fun x => n04Realization_norm_iteratedFDeriv_sqrt_le (ht x) n)

theorem n04Realization_envelope_sqrt_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (f : X → D → ℝ)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (p x))
    (hpos : ∀ x, 0 < f x (p x)) (n : ℕ)
    (hfj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (p x)‖))
    (hinv : HasPositiveEnvelope W (fun x => (f x (p x))⁻¹)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (Real.sqrt ∘ f x) (p x)‖) := by
  have hval : HasPositiveEnvelope W (fun x => f x (p x)) := by
    apply (hfj 0 (Nat.zero_le n)).mono
    intro x
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using le_abs_self (f x (p x))
  exact n04Realization_envelope_comp_jets hW p (fun _ => Real.sqrt) f
    (fun x => contDiffAt_id.sqrt (hpos x).ne') hf n
    (fun j _ => n04Realization_envelope_sqrt_outer_jets hW hpos hval hinv j)
    (fun j _ hj => hfj j hj)

end ContinuousFlexibility.Analysis
