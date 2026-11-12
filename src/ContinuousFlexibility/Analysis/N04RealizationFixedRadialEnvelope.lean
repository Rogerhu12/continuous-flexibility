import ContinuousFlexibility.Analysis.MaterialCoordinateParameterDerivatives
import ContinuousFlexibility.Analysis.N04RealizationEnvelopeDifferential

/-!
# Material envelopes for the existing fixed radial chain coefficients

The existing coefficient recurrence uses addition, multiplication and a
derivative. Uniform envelopes for the positive jets of the fixed radial
map therefore control its coefficients and their finite mass. No bound
on the value of the radial map is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- Uniform positive jets of the fixed radial map control all spatial
jets of its existing chain coefficients. The index may include both a
piece and its actual evaluation point. -/
theorem n04Realization_radialChainCoefficient_envelope
    {X : Type*} {E : X → ℝ} (hE : ∀ x, 1 ≤ E x)
    (p : X → ℝ) (χ : X → ℝ → ℝ) (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (hjets : ∀ j : ℕ, 0 < j → HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ j (χ x) (p x)‖)) :
    ∀ n : ℕ, ∀ i : Fin (n + 1), ∀ d : ℕ, HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ d (radialChainCoefficient (χ x) n i) (p x)‖) := by
  intro n
  induction n with
  | zero =>
      intro i d
      cases d with
      | zero =>
          simpa only [radialChainCoefficient, norm_iteratedFDeriv_zero, norm_one] using
            hasPositiveEnvelope_const E hE 1
      | succ d =>
          simpa only [radialChainCoefficient, iteratedFDeriv_succ_const,
            Pi.zero_apply, norm_zero] using hasPositiveEnvelope_const E hE 0
  | succ n ih =>
      intro i d
      let A : X → Fin (n + 1) → ℝ → ℝ :=
        fun x j => deriv (radialChainCoefficient (χ x) n j)
      let B : X → Fin (n + 1) → ℝ → ℝ :=
        fun x j y => radialChainCoefficient (χ x) n j y * deriv (χ x) y
      let L : X → Fin (n + 2) → ℝ → ℝ := fun x =>
        Fin.snoc (α := fun _ : Fin (n + 2) => ℝ → ℝ) (A x) (fun _ => 0)
      let R : X → Fin (n + 2) → ℝ → ℝ := fun x =>
        Fin.cons (α := fun _ : Fin (n + 2) => ℝ → ℝ) (fun _ => 0) (B x)
      have hA (x : X) (j : Fin (n + 1)) : ContDiff ℝ ∞ (A x j) :=
        (contDiff_infty_iff_deriv.mp (radialChainCoefficient_contDiff (hχ x) n j)).2
      have hB (x : X) (j : Fin (n + 1)) : ContDiff ℝ ∞ (B x j) :=
        (radialChainCoefficient_contDiff (hχ x) n j).mul
          (contDiff_infty_iff_deriv.mp (hχ x)).2
      have hL (x : X) (j : Fin (n + 2)) : ContDiff ℝ ∞ (L x j) := by
        refine Fin.lastCases ?_ (fun l => ?_) j
        · simpa only [L, Fin.snoc_last] using
            (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
        · simpa only [L, Fin.snoc_castSucc] using hA x l
      have hR (x : X) (j : Fin (n + 2)) : ContDiff ℝ ∞ (R x j) := by
        refine Fin.cases ?_ (fun l => ?_) j
        · simpa only [R, Fin.cons_zero] using
            (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
        · simpa only [R, Fin.cons_succ] using hB x l
      have hzero : HasPositiveEnvelope E
          (fun x => ‖iteratedFDeriv ℝ d (fun _ : ℝ => (0 : ℝ)) (p x)‖) := by
        cases d with
        | zero => simpa only [norm_iteratedFDeriv_zero, norm_zero] using
            hasPositiveEnvelope_const E hE 0
        | succ d => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using
            hasPositiveEnvelope_const E hE 0
      have hLjet (j : Fin (n + 2)) : HasPositiveEnvelope E
          (fun x => ‖iteratedFDeriv ℝ d (L x j) (p x)‖) := by
        refine Fin.lastCases ?_ (fun l => ?_) j
        · simpa only [L, Fin.snoc_last] using hzero
        · simpa only [L, A, Fin.snoc_castSucc,
            norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ'] using ih l (d + 1)
      have hRjet (j : Fin (n + 2)) : HasPositiveEnvelope E
          (fun x => ‖iteratedFDeriv ℝ d (R x j) (p x)‖) := by
        refine Fin.cases ?_ (fun l => ?_) j
        · simpa only [R, Fin.cons_zero] using hzero
        · have hb := n04Realization_envelope_mul_jets hE p
            (fun x => radialChainCoefficient (χ x) n l) (fun x => deriv (χ x))
            (fun x => (radialChainCoefficient_contDiff (hχ x) n l).contDiffAt)
            (fun x => (contDiff_infty_iff_deriv.mp (hχ x)).2.contDiffAt) d
            (fun j _ => ih l j) (fun j _ => by
              simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
                ← iteratedDeriv_succ'] using hjets (j + 1) (by omega))
          simpa only [R, B, Fin.cons_succ] using hb
      have hadd := n04Realization_envelope_add_jets hE p (fun x => L x i) (fun x => R x i)
        (fun x => (hL x i).contDiffAt) (fun x => (hR x i).contDiffAt) d (hLjet i) (hRjet i)
      have heq (x : X) : radialChainCoefficient (χ x) (n + 1) i =
          (fun y => L x i y + R x i y) := by
        funext y
        simp only [radialChainCoefficient, L, R, A, B, Pi.add_apply]
      simpa only [heq] using hadd

/-- The complete finite coefficient mass is uniformly bounded by a
power of the same material envelope. -/
theorem n04Realization_radialChainCoefficientMass_envelope
    {X : Type*} {E : X → ℝ} (hE : ∀ x, 1 ≤ E x)
    (p : X → ℝ) (χ : X → ℝ → ℝ) (hχ : ∀ x, ContDiff ℝ ∞ (χ x))
    (hjets : ∀ j : ℕ, 0 < j → HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ j (χ x) (p x)‖)) (n : ℕ) :
    HasPositiveEnvelope E
      (fun x => ∑ i : Fin (n + 1), |radialChainCoefficient (χ x) n i (p x)|) := by
  classical
  apply hasPositiveEnvelope_finsetSum hE Finset.univ
  intro i _
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
    n04Realization_radialChainCoefficient_envelope hE p χ hχ hjets n i 0

end ContinuousFlexibility.Analysis
