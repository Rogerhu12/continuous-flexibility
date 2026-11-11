import ContinuousFlexibility.Analysis.N05ReferenceSymbols

/-!
# Centered quadratic tests for canonical reference symbols

Three actual centered coordinate polynomials identify the three entries
of the transported principal matrix. Taking its determinant cancels the
Jacobian and gives the exact height-factor identity on a negative piece.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n05PrincipalPair_sub_const
    {L : SymmetricCoefficients} {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a b : ℝ) :
    n05PrincipalPair L (fun y => f y - a) (fun y => g y - b) x =
      n05PrincipalPair L f g x := by
  simp only [n05PrincipalPair, radialPartial_sub hf (differentiableAt_const a),
    angularPartial_sub hf (differentiableAt_const a),
    radialPartial_sub hg (differentiableAt_const b),
    angularPartial_sub hg (differentiableAt_const b),
    radialPartial_const, angularPartial_const, sub_zero]

/-- The three entries of the actual transported principal matrix. -/
theorem n05_principal_coefficients_of_conjugation
    {L A : SymmetricCoefficients} {Ψ : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint} {v : ℝ}
    (hLa : ContDiffAt ℝ ∞ L.a x) (hLb : ContDiffAt ℝ ∞ L.b x)
    (hLc : ContDiffAt ℝ ∞ L.c x)
    (hAa : ContDiffAt ℝ ∞ A.a (Ψ x)) (hAb : ContDiffAt ℝ ∞ A.b (Ψ x))
    (hAc : ContDiffAt ℝ ∞ A.c (Ψ x))
    (hh : ContDiffAt ℝ ∞ h x) (hΨ : ContDiffAt ℝ ∞ Ψ x)
    (hJ : planeJacobian Ψ x ≠ 0)
    (hoperator : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x / |planeJacobian Ψ x| *
          divergenceOperator L (fun y => h y * W (Ψ y)) x =
        divergenceOperator A W (Ψ x) + v * W (Ψ x)) :
    h x ^ 2 *
        n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).1) x =
      |planeJacobian Ψ x| * A.a (Ψ x) ∧
    h x ^ 2 *
        n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).2) x =
      |planeJacobian Ψ x| * A.b (Ψ x) ∧
    h x ^ 2 *
        n05PrincipalPair L (fun y => (Ψ y).2) (fun y => (Ψ y).2) x =
      |planeJacobian Ψ x| * A.c (Ψ x) := by
  have hf : ContDiff ℝ ∞ (fun y : PolarPoint => y.1 - (Ψ x).1) :=
    contDiff_fst.sub contDiff_const
  have hg : ContDiff ℝ ∞ (fun y : PolarPoint => y.2 - (Ψ x).2) :=
    contDiff_snd.sub contDiff_const
  have df : DifferentiableAt ℝ (fun y => (Ψ y).1) x :=
    hΨ.fst.differentiableAt (by simp)
  have dg : DifferentiableAt ℝ (fun y => (Ψ y).2) x :=
    hΨ.snd.differentiableAt (by simp)
  have hrr := n05_principalPair_of_conjugation hLa hLb hLc hAa hAb hAc
    hh hΨ hJ hoperator hf hf (sub_self _) (sub_self _)
  have hrt := n05_principalPair_of_conjugation hLa hLb hLc hAa hAb hAc
    hh hΨ hJ hoperator hf hg (sub_self _) (sub_self _)
  have htt := n05_principalPair_of_conjugation hLa hLb hLc hAa hAb hAc
    hh hΨ hJ hoperator hg hg (sub_self _) (sub_self _)
  rw [n05PrincipalPair_sub_const df df,
    n05PrincipalPair_sub_const differentiableAt_fst differentiableAt_fst] at hrr
  rw [n05PrincipalPair_sub_const df dg,
    n05PrincipalPair_sub_const differentiableAt_fst differentiableAt_snd] at hrt
  rw [n05PrincipalPair_sub_const dg dg,
    n05PrincipalPair_sub_const differentiableAt_snd differentiableAt_snd] at htt
  refine ⟨?_, ?_, ?_⟩
  · simpa [n05PrincipalPair] using hrr
  · simpa [n05PrincipalPair] using hrt
  · simpa [n05PrincipalPair] using htt

/-- The determinant identity uses the actual Frechet Jacobian. -/
theorem n05_principalPair_coordinate_determinant
    (L : SymmetricCoefficients) {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hΨ : DifferentiableAt ℝ Ψ x) :
    n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).1) x *
        n05PrincipalPair L (fun y => (Ψ y).2) (fun y => (Ψ y).2) x -
      n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).2) x ^ 2 =
        (L.a x * L.c x - L.b x ^ 2) * planeJacobian Ψ x ^ 2 := by
  rw [n05_planeJacobian_eq_partials hΨ]
  unfold n05PrincipalPair
  convert n05_principal_determinant_algebra (L.a x) (L.b x) (L.c x)
    (radialPartial (fun y => (Ψ y).1) x)
    (angularPartial (fun y => (Ψ y).1) x)
    (radialPartial (fun y => (Ψ y).2) x)
    (angularPartial (fun y => (Ψ y).2) x) using 1 <;> ring

/-- In two dimensions the Jacobian cancels from the determinant of the
height-conjugated principal matrix. -/
theorem n05_determinant_of_conjugation
    {L A : SymmetricCoefficients} {Ψ : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint} {v : ℝ}
    (hLa : ContDiffAt ℝ ∞ L.a x) (hLb : ContDiffAt ℝ ∞ L.b x)
    (hLc : ContDiffAt ℝ ∞ L.c x)
    (hAa : ContDiffAt ℝ ∞ A.a (Ψ x)) (hAb : ContDiffAt ℝ ∞ A.b (Ψ x))
    (hAc : ContDiffAt ℝ ∞ A.c (Ψ x))
    (hh : ContDiffAt ℝ ∞ h x) (hΨ : ContDiffAt ℝ ∞ Ψ x)
    (hJ : planeJacobian Ψ x ≠ 0)
    (hoperator : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x / |planeJacobian Ψ x| *
          divergenceOperator L (fun y => h y * W (Ψ y)) x =
        divergenceOperator A W (Ψ x) + v * W (Ψ x)) :
    h x ^ 4 * (L.a x * L.c x - L.b x ^ 2) =
      A.a (Ψ x) * A.c (Ψ x) - A.b (Ψ x) ^ 2 := by
  obtain ⟨hrr, hrt, htt⟩ := n05_principal_coefficients_of_conjugation
    hLa hLb hLc hAa hAb hAc hh hΨ hJ hoperator
  have hdet := n05_principalPair_coordinate_determinant L
    (hΨ.differentiableAt (by simp))
  have hscaled :
      (h x ^ 4 * (L.a x * L.c x - L.b x ^ 2)) * planeJacobian Ψ x ^ 2 =
        (A.a (Ψ x) * A.c (Ψ x) - A.b (Ψ x) ^ 2) * planeJacobian Ψ x ^ 2 := by
    calc
      _ = h x ^ 4 *
          (n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).1) x *
              n05PrincipalPair L (fun y => (Ψ y).2) (fun y => (Ψ y).2) x -
            n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).2) x ^ 2) := by
        rw [hdet]
        ring
      _ = (h x ^ 2 *
            n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).1) x) *
            (h x ^ 2 *
              n05PrincipalPair L (fun y => (Ψ y).2) (fun y => (Ψ y).2) x) -
          (h x ^ 2 *
            n05PrincipalPair L (fun y => (Ψ y).1) (fun y => (Ψ y).2) x) ^ 2 := by ring
      _ = (|planeJacobian Ψ x| * A.a (Ψ x)) *
            (|planeJacobian Ψ x| * A.c (Ψ x)) -
          (|planeJacobian Ψ x| * A.b (Ψ x)) ^ 2 := by rw [hrr, hrt, htt]
      _ = _ := by
        rw [← sq_abs (planeJacobian Ψ x)]
        ring
  exact mul_right_cancel₀ (pow_ne_zero 2 hJ) hscaled

/-- The actual reference principal coefficients on a negative cylinder. -/
def n05TricomiCoefficients : SymmetricCoefficients where
  a := fun _ => 1
  b := fun _ => 0
  c := fun p => -p.1

/-- The negative canonical identity forces the exact height-factor
relation with the physical determinant. -/
theorem n05_negative_height_determinant
    {L : SymmetricCoefficients} {Ψ : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint} {v : ℝ}
    (hLa : ContDiffAt ℝ ∞ L.a x) (hLb : ContDiffAt ℝ ∞ L.b x)
    (hLc : ContDiffAt ℝ ∞ L.c x)
    (hh : ContDiffAt ℝ ∞ h x) (hΨ : ContDiffAt ℝ ∞ Ψ x)
    (hJ : planeJacobian Ψ x ≠ 0)
    (hoperator : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      h x / |planeJacobian Ψ x| *
          divergenceOperator L (fun y => h y * W (Ψ y)) x =
        divergenceOperator n05TricomiCoefficients W (Ψ x) + v * W (Ψ x)) :
    h x ^ 4 * (L.a x * L.c x - L.b x ^ 2) = -(Ψ x).1 := by
  have ha : ContDiffAt ℝ ∞ n05TricomiCoefficients.a (Ψ x) := contDiffAt_const
  have hb : ContDiffAt ℝ ∞ n05TricomiCoefficients.b (Ψ x) := contDiffAt_const
  have hc : ContDiffAt ℝ ∞ n05TricomiCoefficients.c (Ψ x) := contDiffAt_fst.neg
  simpa [n05TricomiCoefficients] using
    n05_determinant_of_conjugation hLa hLb hLc ha hb hc hh hΨ hJ hoperator

end ContinuousFlexibility.Statements
