module

public import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback

/-!
# Recovering the effective principal coefficients from actual operator values

The corrected carré-du-champ expression eliminates both first-order terms
and an arbitrary scalar potential. Six actual coordinate-test evaluations
then determine the three entries of a smooth effective principal matrix.
The comparison operator can be completely arbitrary: no regularity of any
coefficients used to store that operator is assumed or inferred.

These are local operator statements. Applying them to a restricted class
of test fields still requires genuine local extensions into that class.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The corrected product defect, defined for any actual operator. The
constant test cancels a possible zero-order term. -/
def n04bCarre
    (P : (PolarPoint → ℝ) → PolarPoint → ℝ)
    (f g : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  (P (fun y => f y * g y) x - f x * P g x - g x * P f x +
    f x * g x * P (fun _ => 1) x) / 2

/-- This constant-test identity requires no regularity of the stored
coefficient functions. -/
theorem n04b_divergenceOperator_one (A : SymmetricCoefficients)
    (x : PolarPoint) :
    divergenceOperator A (fun _ => 1) x = 0 := by
  simp [divergenceOperator]

/-- The actual product rule for a smooth divergence operator. All first-
order contributions cancel; only its principal bilinear form remains. -/
theorem n04b_divergenceOperator_product
    {A : SymmetricCoefficients} {f g : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    divergenceOperator A (fun y => f y * g y) x -
        f x * divergenceOperator A g x - g x * divergenceOperator A f x =
      2 * (A.a x * radialPartial f x * radialPartial g x +
        A.b x * (radialPartial f x * angularPartial g x +
          angularPartial f x * radialPartial g x) +
        A.c x * angularPartial f x * angularPartial g x) := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  simp only [divergenceOperator]
  rw [divergence_expansion_of_coefficients ha hb hc (hf.mul hg),
    divergence_expansion_of_coefficients ha hb hc hg,
    divergence_expansion_of_coefficients ha hb hc hf]
  unfold radialPartial angularPartial
  simp only [polar_directional_mul hf1 hg1,
    polar_second_directional_mul hf hg]
  ring

/-- The scalar potential is allowed to be arbitrary; its actual value
cancels in the corrected carré-du-champ expression. -/
theorem n04b_carre_divergence_potential
    {A : SymmetricCoefficients} {V f g : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    n04bCarre (fun u y => divergenceOperator A u y + V y * u y) f g x =
      A.a x * radialPartial f x * radialPartial g x +
        A.b x * (radialPartial f x * angularPartial g x +
          angularPartial f x * radialPartial g x) +
        A.c x * angularPartial f x * angularPartial g x := by
  have h := n04b_divergenceOperator_product ha hb hc hf hg
  dsimp only [n04bCarre]
  rw [n04b_divergenceOperator_one]
  linear_combination h / 2

/-- A principal matrix extracted from six operator evaluations at each
point. This definition makes sense even when the operator is not linear. -/
def n04bRecoveredPrincipal
    (P : (PolarPoint → ℝ) → PolarPoint → ℝ) : SymmetricCoefficients where
  a x := n04bCarre P Prod.fst Prod.fst x
  b x := n04bCarre P Prod.fst Prod.snd x
  c x := n04bCarre P Prod.snd Prod.snd x

/-- For an actual smooth divergence operator with any potential, the
recovered matrix equals its actual principal coefficient values. -/
theorem n04b_recoveredPrincipal_divergence_potential
    {A : SymmetricCoefficients} {V : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x) :
    (n04bRecoveredPrincipal
      (fun u y => divergenceOperator A u y + V y * u y)).a x = A.a x ∧
    (n04bRecoveredPrincipal
      (fun u y => divergenceOperator A u y + V y * u y)).b x = A.b x ∧
    (n04bRecoveredPrincipal
      (fun u y => divergenceOperator A u y + V y * u y)).c x = A.c x := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [n04bRecoveredPrincipal] using
      (n04b_carre_divergence_potential (V := V) ha hb hc
        (f := Prod.fst) (g := Prod.fst) contDiffAt_fst contDiffAt_fst)
  · simpa [n04bRecoveredPrincipal] using
      (n04b_carre_divergence_potential (V := V) ha hb hc
        (f := Prod.fst) (g := Prod.snd) contDiffAt_fst contDiffAt_snd)
  · simpa [n04bRecoveredPrincipal] using
      (n04b_carre_divergence_potential (V := V) ha hb hc
        (f := Prod.snd) (g := Prod.snd) contDiffAt_snd contDiffAt_snd)

/-- Equality on exactly six actual test evaluations transfers the
recovered matrix. Neither operator carries a regularity hypothesis. -/
theorem n04b_recoveredPrincipal_eq_of_six_evaluations
    {P Q : (PolarPoint → ℝ) → PolarPoint → ℝ} {x : PolarPoint}
    (h1 : P (fun _ => 1) x = Q (fun _ => 1) x)
    (hr : P Prod.fst x = Q Prod.fst x)
    (ht : P Prod.snd x = Q Prod.snd x)
    (hrr : P (fun y => y.1 * y.1) x = Q (fun y => y.1 * y.1) x)
    (hrt : P (fun y => y.1 * y.2) x = Q (fun y => y.1 * y.2) x)
    (htt : P (fun y => y.2 * y.2) x = Q (fun y => y.2 * y.2) x) :
    (n04bRecoveredPrincipal P).a x = (n04bRecoveredPrincipal Q).a x ∧
      (n04bRecoveredPrincipal P).b x = (n04bRecoveredPrincipal Q).b x ∧
      (n04bRecoveredPrincipal P).c x = (n04bRecoveredPrincipal Q).c x := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [n04bRecoveredPrincipal, n04bCarre, h1, hr, ht, hrr, hrt, htt]

/-- Finite-test recovery of a smooth effective field. The six hypotheses
refer only to actual values of the other operator P. In particular, this
does not assert regularity or identification of a stored representation
of P by possibly nonsmooth coefficient functions. -/
theorem n04b_effectivePrincipal_of_six_evaluations
    {P : (PolarPoint → ℝ) → PolarPoint → ℝ}
    {A : SymmetricCoefficients} {V : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (h1 : P (fun _ => 1) x =
      divergenceOperator A (fun _ => 1) x + V x)
    (hr : P Prod.fst x = divergenceOperator A Prod.fst x + V x * x.1)
    (ht : P Prod.snd x = divergenceOperator A Prod.snd x + V x * x.2)
    (hrr : P (fun y => y.1 * y.1) x =
      divergenceOperator A (fun y => y.1 * y.1) x + V x * (x.1 * x.1))
    (hrt : P (fun y => y.1 * y.2) x =
      divergenceOperator A (fun y => y.1 * y.2) x + V x * (x.1 * x.2))
    (htt : P (fun y => y.2 * y.2) x =
      divergenceOperator A (fun y => y.2 * y.2) x + V x * (x.2 * x.2)) :
    (n04bRecoveredPrincipal P).a x = A.a x ∧
      (n04bRecoveredPrincipal P).b x = A.b x ∧
      (n04bRecoveredPrincipal P).c x = A.c x := by
  let Q : (PolarPoint → ℝ) → PolarPoint → ℝ :=
    fun u y => divergenceOperator A u y + V y * u y
  have h1' : P (fun _ => 1) x = Q (fun _ => 1) x := by
    simpa only [Q, mul_one] using h1
  have heq := n04b_recoveredPrincipal_eq_of_six_evaluations
    (P := P) (Q := Q) h1' hr ht hrr hrt htt
  have hA := n04b_recoveredPrincipal_divergence_potential (V := V) ha hb hc
  exact ⟨heq.1.trans hA.1, heq.2.1.trans hA.2.1, heq.2.2.trans hA.2.2⟩

end ContinuousFlexibility.Analysis
