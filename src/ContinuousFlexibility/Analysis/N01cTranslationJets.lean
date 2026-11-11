import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameter derivatives of translated evaluation

This audit module isolates the extra spatial derivatives created by varying a
translation parameter.  A fixed finite collection of uniform spatial derivative
bounds does not control all parameter derivatives, even for smooth, even,
pi-periodic Fourier modes.

The mixed expression below is the linearized endpoint expression in a two-stage
circle flow (a translation followed by a varied vector field).  We prove the
derivative identities and the explicit Fourier obstruction here; we do not assert
that every such varied vector field is a characteristic speed of the nonlinear
surface problem.  In particular this file does not prove `¬ N01Statement`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N01cAudit

open scoped ContDiff

/-- Evaluation at a translated argument. -/
def translatedEvaluation (h : ℝ → ℝ) (θ a : ℝ) : ℝ := h (θ + a)

theorem translatedEvaluation_apply (h : ℝ → ℝ) (θ a : ℝ) :
    translatedEvaluation h θ a = h (θ + a) := rfl

/-- Each translation derivative is the corresponding spatial derivative. -/
theorem iteratedDeriv_translatedEvaluation (k : ℕ) (h : ℝ → ℝ) (θ a : ℝ) :
    iteratedDeriv k (translatedEvaluation h θ) a = iteratedDeriv k h (θ + a) := by
  simpa only [translatedEvaluation_apply] using
    congrFun (iteratedDeriv_comp_const_add k h θ) a

/-- For a smooth function these are genuine derivatives at every parameter. -/
theorem hasDerivAt_translationJet {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (k : ℕ) (θ a : ℝ) :
    HasDerivAt (fun t => iteratedDeriv k (translatedEvaluation h θ) t)
      (iteratedDeriv (k + 1) h (θ + a)) a := by
  have hd : Differentiable ℝ (iteratedDeriv k h) :=
    hh.differentiable_iteratedDeriv k
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
  have hshift := HasDerivAt.comp_const_add θ a ((hd (θ + a)).hasDerivAt)
  simpa only [iteratedDeriv_translatedEvaluation, iteratedDeriv_succ] using hshift

/-- The first variation in a vector-field amplitude after translation. -/
def translationProbe (h : ℝ → ℝ) (θ a b : ℝ) : ℝ := b * h (θ + a)

theorem translationProbe_apply (h : ℝ → ℝ) (θ a b : ℝ) :
    translationProbe h θ a b = b * h (θ + a) := rfl

theorem hasDerivAt_translationProbe (h : ℝ → ℝ) (θ a b : ℝ) :
    HasDerivAt (translationProbe h θ a) (h (θ + a)) b := by
  simpa only [translationProbe_apply, one_mul] using
    (hasDerivAt_id b).mul_const (h (θ + a))

theorem deriv_translationProbe (h : ℝ → ℝ) (θ a b : ℝ) :
    deriv (translationProbe h θ a) b = h (θ + a) :=
  (hasDerivAt_translationProbe h θ a b).deriv

/-- One amplitude derivative and `k` translation derivatives require the
`k`th spatial derivative of the varied function. -/
theorem mixedDeriv_translationProbe (k : ℕ) (h : ℝ → ℝ) (θ a : ℝ) :
    iteratedDeriv k (fun t => deriv (translationProbe h θ t) 0) a =
      iteratedDeriv k h (θ + a) := by
  simp only [deriv_translationProbe]
  exact congrFun (iteratedDeriv_comp_const_add k h θ) a

/-- The unit ball described by all uniform derivative bounds through order `L`.
This is an explicit finite-order control, without an implicit norm convention. -/
def FiniteJetUnit (L : ℕ) (h : ℝ → ℝ) : Prop :=
  ∀ j : ℕ, j ≤ L → ∀ θ : ℝ, |iteratedDeriv j h θ| ≤ 1

/-- A normalized even Fourier mode of period pi and frequency `2 * (n + 1)`. -/
def normalizedCosMode (L n : ℕ) (θ : ℝ) : ℝ :=
  Real.cos ((2 * ((n : ℝ) + 1)) * θ) / (2 * ((n : ℝ) + 1)) ^ L

theorem normalizedCosMode_apply (L n : ℕ) (θ : ℝ) :
    normalizedCosMode L n θ =
      Real.cos ((2 * ((n : ℝ) + 1)) * θ) / (2 * ((n : ℝ) + 1)) ^ L := rfl

theorem contDiff_normalizedCosMode (L n : ℕ) :
    ContDiff ℝ ∞ (normalizedCosMode L n) := by
  exact ((contDiff_const.mul contDiff_id).cos).div_const _

theorem even_normalizedCosMode (L n : ℕ) : Function.Even (normalizedCosMode L n) := by
  intro θ
  simp only [normalizedCosMode_apply, mul_neg, Real.cos_neg]

theorem periodic_normalizedCosMode (L n : ℕ) :
    Function.Periodic (normalizedCosMode L n) Real.pi := by
  intro θ
  rw [normalizedCosMode_apply, normalizedCosMode_apply]
  congr 1
  have hid : (2 * ((n : ℝ) + 1)) * (θ + Real.pi) =
      (2 * ((n : ℝ) + 1)) * θ + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [hid, Real.cos_add_nat_mul_two_pi]

theorem iteratedDeriv_normalizedCosMode (L n j : ℕ) (θ : ℝ) :
    iteratedDeriv j (normalizedCosMode L n) θ =
      (2 * ((n : ℝ) + 1)) ^ j *
        iteratedDeriv j Real.cos ((2 * ((n : ℝ) + 1)) * θ) /
          (2 * ((n : ℝ) + 1)) ^ L := by
  rw [show normalizedCosMode L n =
      fun t : ℝ => Real.cos ((2 * ((n : ℝ) + 1)) * t) /
        (2 * ((n : ℝ) + 1)) ^ L from funext (normalizedCosMode_apply L n)]
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_comp_const_mul (Real.contDiff_cos : ContDiff ℝ j Real.cos)]

/-- All spatial derivatives through the normalization order are uniformly at
most one, independently of the frequency. -/
theorem finiteJetUnit_normalizedCosMode (L n : ℕ) :
    FiniteJetUnit L (normalizedCosMode L n) := by
  intro j hj θ
  have hω : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hω0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := lt_of_lt_of_le zero_lt_one hω
  rw [iteratedDeriv_normalizedCosMode, abs_div, abs_mul,
    abs_of_nonneg (pow_nonneg hω0.le _), abs_of_nonneg (pow_nonneg hω0.le _)]
  calc
    (2 * ((n : ℝ) + 1)) ^ j *
          |iteratedDeriv j Real.cos ((2 * ((n : ℝ) + 1)) * θ)| /
        (2 * ((n : ℝ) + 1)) ^ L ≤
        (2 * ((n : ℝ) + 1)) ^ j / (2 * ((n : ℝ) + 1)) ^ L := by
      exact div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.abs_iteratedDeriv_cos_le_one j ((2 * ((n : ℝ) + 1)) * θ))
          (pow_nonneg hω0.le j)) (pow_nonneg hω0.le L)
    _ ≤ 1 := (div_le_one (pow_pos hω0 L)).2 (pow_le_pow_right₀ hω hj)

/-- At the next sufficiently large even order the same modes have exact
polynomial growth in their frequency. -/
theorem highJet_normalizedCosMode (L n : ℕ) :
    |iteratedDeriv (2 * (L + 1)) (normalizedCosMode L n) 0| =
      (2 * ((n : ℝ) + 1)) ^ (L + 2) := by
  have hω0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  rw [iteratedDeriv_normalizedCosMode, mul_zero, Real.iteratedDeriv_even_cos]
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.cos_zero,
    mul_one, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_pos hω0]
  rw [show 2 * (L + 1) = L + (L + 2) by omega, pow_add]
  exact mul_div_cancel_left₀ _ (pow_ne_zero L hω0.ne')

/-- No finite spatial derivative control bounds all translation parameter jets.
For each finite order `L`, one fixed higher parameter order is already unbounded
on the smooth even periodic functions in `FiniteJetUnit L`. -/
theorem unbounded_translationJets (L : ℕ) :
    ∃ k : ℕ, ∀ B : ℝ, ∃ h : ℝ → ℝ,
      ContDiff ℝ ∞ h ∧ Function.Even h ∧ Function.Periodic h Real.pi ∧
      FiniteJetUnit L h ∧
      B < |iteratedDeriv k (fun a => deriv (translationProbe h 0 a) 0) 0| := by
  refine ⟨2 * (L + 1), fun B => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨normalizedCosMode L n, contDiff_normalizedCosMode L n,
    even_normalizedCosMode L n, periodic_normalizedCosMode L n,
    finiteJetUnit_normalizedCosMode L n, ?_⟩
  rw [mixedDeriv_translationProbe, zero_add, highJet_normalizedCosMode]
  have hω : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hB : B < 2 * ((n : ℝ) + 1) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  exact hB.trans_le (le_self_pow₀ hω (by omega))

/-- Allowing a different bound for each parameter order still does not make a
fixed finite spatial order sufficient. -/
theorem not_all_translationJets_bounded (L : ℕ) :
    ¬ (∀ k : ℕ, ∃ B : ℝ, ∀ h : ℝ → ℝ,
      ContDiff ℝ ∞ h → Function.Even h → Function.Periodic h Real.pi →
      FiniteJetUnit L h →
      |iteratedDeriv k (fun a => deriv (translationProbe h 0 a) 0) 0| ≤ B) := by
  intro hbounded
  obtain ⟨k, hk⟩ := unbounded_translationJets L
  obtain ⟨B, hB⟩ := hbounded k
  obtain ⟨h, hsmooth, heven, hperiodic, hjets, hlarge⟩ := hk B
  exact (not_lt_of_ge (hB h hsmooth heven hperiodic hjets)) hlarge

end ContinuousFlexibility.Analysis.N01cAudit
