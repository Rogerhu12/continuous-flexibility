import ContinuousFlexibility.Analysis.PointwiseCylinderJets
import ContinuousFlexibility.Analysis.BoundaryMixedJets
import ContinuousFlexibility.Analysis.CylinderSobolev

/-!
# Finite conformal coordinate data at a regular positive boundary

The actual radial jets of the two scalar coefficients d and e determine
coordinate jets by the finite recursion F_r = [[e,d],[-d,e]] F_θ.
The zeroth coordinate is (v,θ). A finite Taylor polynomial realizes these
data, and its actual residual has all radial jets below the Taylor
degree equal to zero. No equation on an open collar is assumed or solved.

Degree three is sufficient for the order-two principal-density matching
used at an artificial endpoint of a positive component.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The two scalar components are indexed by false (radial) and true
(angular). The recursion uses only earlier, actual angular derivatives. -/
def positiveConformalBoundaryData (D E : ℕ → ℝ → ℝ) (v : ℝ) :
    ℕ → Bool → ℝ → ℝ
  | 0, side, θ => if side then θ else v
  | n + 1, side, θ =>
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        (E j θ * deriv (positiveConformalBoundaryData D E v (n - j) side) θ +
          (if side then -D j θ else D j θ) *
            deriv (positiveConformalBoundaryData D E v (n - j) (!side)) θ)
termination_by n _ _ => n
decreasing_by all_goals omega

private theorem positiveConformalBoundaryData_zero_fun
    (D E : ℕ → ℝ → ℝ) (v : ℝ) (side : Bool) :
    positiveConformalBoundaryData D E v 0 side =
      (fun θ => if side then θ else v) := by
  funext θ
  rw [positiveConformalBoundaryData]

theorem contDiff_positiveConformalBoundaryData
    {D E : ℕ → ℝ → ℝ} (hD : ∀ j, ContDiff ℝ ∞ (D j))
    (hE : ∀ j, ContDiff ℝ ∞ (E j)) (v : ℝ) (n : ℕ) (side : Bool) :
    ContDiff ℝ ∞ (positiveConformalBoundaryData D E v n side) := by
  induction n using Nat.strong_induction_on generalizing side with
  | h n ih =>
      cases n with
      | zero =>
          rw [positiveConformalBoundaryData_zero_fun]
          cases side
          · exact contDiff_const
          · exact contDiff_id
      | succ n =>
          have hprev (j : ℕ) (s : Bool) :
              ContDiff ℝ ∞ (deriv (positiveConformalBoundaryData D E v (n - j) s)) :=
            (contDiff_infty_iff_deriv.mp (ih (n - j) (by omega) s)).2
          have hstep : positiveConformalBoundaryData D E v (n + 1) side =
              (fun θ => ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
                (E j θ * deriv (positiveConformalBoundaryData D E v (n - j) side) θ +
                  (if side then -D j θ else D j θ) *
                    deriv (positiveConformalBoundaryData D E v (n - j) (!side)) θ)) := by
            funext θ
            rw [positiveConformalBoundaryData]
          rw [hstep]
          cases side
          · simp only [Bool.not_false, Bool.false_eq_true,
              ↓reduceIte]
            apply ContDiff.sum
            intro j _
            exact contDiff_const.mul (((hE j).mul (hprev j false)).add
              ((hD j).mul (hprev j true)))
          · simp only [Bool.not_true, ↓reduceIte]
            apply ContDiff.sum
            intro j _
            exact contDiff_const.mul (((hE j).mul (hprev j true)).add
              ((hD j).neg.mul (hprev j false)))

def positiveConformalBoundaryPolynomial (N : ℕ) (c v : ℝ)
    (d e : PolarPoint → ℝ) (side : Bool) : PolarPoint → ℝ :=
  boundaryTaylorPolynomial N c
    (fun j => positiveConformalBoundaryData
      (radialBoundaryJet d c) (radialBoundaryJet e c) v j side)

theorem contDiff_positiveConformalBoundaryPolynomial
    {d e : PolarPoint → ℝ} {c : ℝ}
    (hd : ∀ θ, ContDiffAt ℝ ∞ d (c, θ))
    (he : ∀ θ, ContDiffAt ℝ ∞ e (c, θ)) (N : ℕ) (v : ℝ) (side : Bool) :
    ContDiff ℝ ∞ (positiveConformalBoundaryPolynomial N c v d e side) :=
  contDiff_boundaryTaylorPolynomial (fun j _ =>
    contDiff_positiveConformalBoundaryData
      (contDiff_radialBoundaryJet_of_contDiffAt c hd)
      (contDiff_radialBoundaryJet_of_contDiffAt c he) v j side) c

theorem radialBoundaryJet_positiveConformalBoundaryPolynomial
    (N : ℕ) (c v : ℝ) (d e : PolarPoint → ℝ) (side : Bool)
    {k : ℕ} (hk : k ≤ N) (θ : ℝ) :
    radialBoundaryJet (positiveConformalBoundaryPolynomial N c v d e side) c k θ =
      positiveConformalBoundaryData
        (radialBoundaryJet d c) (radialBoundaryJet e c) v k side θ :=
  iteratedDeriv_boundaryTaylorPolynomial N c _ hk θ

theorem radialBoundaryJet_radialPartial_of_global
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (k : ℕ) (θ : ℝ) :
    radialBoundaryJet (radialPartial f) c k θ = radialBoundaryJet f c (k + 1) θ := by
  simpa only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero] using
    mixedDerivative_radialPartial isOpen_univ hf.contDiffOn k 0 (mem_univ (c, θ))

theorem radialBoundaryJet_angularPartial_of_global
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (k : ℕ) (θ : ℝ) :
    radialBoundaryJet (angularPartial f) c k θ = deriv (radialBoundaryJet f c k) θ := by
  have h₁ := mixedDerivative_angularPartial isOpen_univ hf.contDiffOn k 0 (mem_univ (c, θ))
  have h₂ := iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
    isOpen_univ hf.contDiffOn c (fun η => mem_univ (c, η)) k 1 θ
  have h₁' : radialBoundaryJet (angularPartial f) c k θ = mixedDerivative k 1 f (c, θ) := by
    simpa only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero, Nat.zero_add] using h₁
  exact h₁'.trans (by simpa only [iteratedDeriv_one] using h₂.symm)

private theorem radialBoundaryJet_mul_at
    {f g : PolarPoint → ℝ} {c θ : ℝ}
    (hf : ContDiffAt ℝ ∞ f (c, θ)) (hg : ContDiffAt ℝ ∞ g (c, θ)) (k : ℕ) :
    radialBoundaryJet (fun p => f p * g p) c k θ =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        radialBoundaryJet f c j θ * radialBoundaryJet g c (k - j) θ := by
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hfs := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ)) (g := f) c hf hline
  have hgs := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ)) (g := g) c hg hline
  simpa only [radialBoundaryJet] using iteratedDeriv_fun_mul
    (hfs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hgs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))

/-- The finite equation is an equality of actual radial jets. In
particular this is stronger than a purely formal polynomial identity. -/
theorem positiveConformalBoundaryPolynomial_equation_jets
    {d e : PolarPoint → ℝ} {c : ℝ}
    (hd : ∀ θ, ContDiffAt ℝ ∞ d (c, θ))
    (he : ∀ θ, ContDiffAt ℝ ∞ e (c, θ)) (N : ℕ) (v : ℝ)
    (side : Bool) {k : ℕ} (hk : k + 1 ≤ N) (θ : ℝ) :
    let P := positiveConformalBoundaryPolynomial N c v d e
    radialBoundaryJet (radialPartial (P side)) c k θ =
      radialBoundaryJet (fun p => e p * angularPartial (P side) p +
        (if side then -d p else d p) * angularPartial (P (!side)) p) c k θ := by
  let P := positiveConformalBoundaryPolynomial N c v d e
  let ds : PolarPoint → ℝ := fun p => if side then -d p else d p
  have hP (s : Bool) : ContDiff ℝ ∞ (P s) :=
    contDiff_positiveConformalBoundaryPolynomial hd he N v s
  have hds : ContDiffAt ℝ ∞ ds (c, θ) := by
    cases side
    · exact hd θ
    · exact (hd θ).neg
  have hsum₀ := (he θ).mul (contDiff_cylinder_angularPartial (hP side)).contDiffAt
  have hsum₁ := hds.mul (contDiff_cylinder_angularPartial (hP (!side))).contDiffAt
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have h₀ := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
    (g := fun p => e p * angularPartial (P side) p) c hsum₀ hline
  have h₁ := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
    (g := fun p => ds p * angularPartial (P (!side)) p) c hsum₁ hline
  have hsum : radialBoundaryJet (fun p => e p * angularPartial (P side) p +
      ds p * angularPartial (P (!side)) p) c k θ =
      radialBoundaryJet (fun p => e p * angularPartial (P side) p) c k θ +
      radialBoundaryJet (fun p => ds p * angularPartial (P (!side)) p) c k θ := by
    simpa only [radialBoundaryJet] using iteratedDeriv_fun_add
      (h₀.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
      (h₁.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
  change radialBoundaryJet (radialPartial (P side)) c k θ = _
  rw [radialBoundaryJet_radialPartial_of_global (hP side),
    radialBoundaryJet_positiveConformalBoundaryPolynomial N c v d e side hk θ]
  change positiveConformalBoundaryData
    (radialBoundaryJet d c) (radialBoundaryJet e c) v (k + 1) side θ = _
  rw [hsum, radialBoundaryJet_mul_at (he θ)
      (contDiff_cylinder_angularPartial (hP side)).contDiffAt,
    radialBoundaryJet_mul_at hds
      (contDiff_cylinder_angularPartial (hP (!side))).contDiffAt,
    ← Finset.sum_add_distrib]
  rw [positiveConformalBoundaryData]
  apply Finset.sum_congr rfl
  intro j hj
  have hrest : k - j ≤ N := (Nat.sub_le k j).trans (by omega)
  have htrace (s : Bool) : radialBoundaryJet (P s) c (k - j) =
      positiveConformalBoundaryData
        (radialBoundaryJet d c) (radialBoundaryJet e c) v (k - j) s := by
    funext η
    exact radialBoundaryJet_positiveConformalBoundaryPolynomial N c v d e s hrest η
  rw [radialBoundaryJet_angularPartial_of_global (hP side),
    radialBoundaryJet_angularPartial_of_global (hP (!side)), htrace side, htrace (!side)]
  have hdjet : radialBoundaryJet ds c j θ =
      if side then -radialBoundaryJet d c j θ else radialBoundaryJet d c j θ := by
    cases side <;> simp only [ds, radialBoundaryJet, Bool.false_eq_true,
      ↓reduceIte, iteratedDeriv_fun_neg]
  rw [hdjet]
  ring

/-- The zeroth coordinate and the first radial derivative have the
required values at either regular boundary. -/
theorem positiveConformalBoundaryPolynomial_first_jets
    {d e : PolarPoint → ℝ} {c : ℝ}
    (hd : ∀ θ, ContDiffAt ℝ ∞ d (c, θ))
    (he : ∀ θ, ContDiffAt ℝ ∞ e (c, θ)) {N : ℕ} (hN : 1 ≤ N)
    (v θ : ℝ) :
    let P := positiveConformalBoundaryPolynomial N c v d e
    P false (c, θ) = v ∧ P true (c, θ) = θ ∧
      radialPartial (P false) (c, θ) = d (c, θ) ∧
      radialPartial (P true) (c, θ) = e (c, θ) := by
  have hzero (s : Bool) := radialBoundaryJet_positiveConformalBoundaryPolynomial
    N c v d e s (Nat.zero_le N) θ
  have hfirst (s : Bool) := radialBoundaryJet_positiveConformalBoundaryPolynomial
    N c v d e s hN θ
  have hP (s : Bool) := contDiff_positiveConformalBoundaryPolynomial hd he N v s
  have hfirst' (s : Bool) :
      radialPartial (positiveConformalBoundaryPolynomial N c v d e s) (c, θ) =
        positiveConformalBoundaryData
          (radialBoundaryJet d c) (radialBoundaryJet e c) v 1 s θ := by
    simpa only [radialBoundaryJet, iteratedDeriv_one,
      deriv_cylinder_radial_slice ((hP s).differentiable (by simp))] using hfirst s
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [radialBoundaryJet, iteratedDeriv_zero, positiveConformalBoundaryData,
      Bool.false_eq_true, ↓reduceIte] using hzero false
  · simpa only [radialBoundaryJet, iteratedDeriv_zero, positiveConformalBoundaryData,
      ↓reduceIte] using hzero true
  · simpa [positiveConformalBoundaryData, positiveConformalBoundaryData_zero_fun,
      radialBoundaryJet] using hfirst' false
  · simpa [positiveConformalBoundaryData, positiveConformalBoundaryData_zero_fun,
      radialBoundaryJet] using hfirst' true

end ContinuousFlexibility.Analysis
