module

public import ContinuousFlexibility.Analysis.AdjugatePrincipalField
public import ContinuousFlexibility.Analysis.FiniteFullJetMatching
public import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction

/-!
# Actual adjugate principal jets from matched transport and height

The physical coefficient field is evaluated at the actual transported
point. Matching the transport through order n+1 and the height through
order n therefore matches the full ordinary principal jets through n.
The proof uses only the forward maps at the boundary.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

private abbrev PrincipalJetInput :=
  PolarPoint × ((PolarPoint →L[ℝ] PolarPoint) × ℝ)

private def principalJetFormula (A : SymmetricCoefficients) (i : Fin 3)
    (w : PrincipalJetInput) : ℝ :=
  let x := w.1
  let M := w.2.1
  let h := w.2.2
  let J := (M (1, 0)).1 * (M (0, 1)).2 - (M (1, 0)).2 * (M (0, 1)).1
  let s := 1 / (h ^ 2 * |J|)
  if i = 0 then s *
    (A.a x * (M (0, 1)).2 ^ 2 + 2 * A.b x * (M (0, 1)).2 * (-(M (0, 1)).1) +
      A.c x * (-(M (0, 1)).1) ^ 2)
  else if i = 1 then s *
    (A.a x * (M (0, 1)).2 * (-(M (1, 0)).2) +
      A.b x * ((M (0, 1)).2 * (M (1, 0)).1 +
        (-(M (0, 1)).1) * (-(M (1, 0)).2)) +
      A.c x * (-(M (0, 1)).1) * (M (1, 0)).1)
  else s *
    (A.a x * (-(M (1, 0)).2) ^ 2 +
      2 * A.b x * (-(M (1, 0)).2) * (M (1, 0)).1 +
      A.c x * (M (1, 0)).1 ^ 2)

private theorem contDiffAt_principalJetFormula
    {A : SymmetricCoefficients} {w : PrincipalJetInput}
    (ha : ContDiffAt ℝ ∞ A.a w.1) (hb : ContDiffAt ℝ ∞ A.b w.1)
    (hc : ContDiffAt ℝ ∞ A.c w.1) (hh : w.2.2 ≠ 0)
    (hJ : (w.2.1 (1, 0)).1 * (w.2.1 (0, 1)).2 -
      (w.2.1 (1, 0)).2 * (w.2.1 (0, 1)).1 ≠ 0) (i : Fin 3) :
    ContDiffAt ℝ ∞ (principalJetFormula A i) w := by
  have hr : ContDiffAt ℝ ∞ (fun v : PrincipalJetInput => v.2.1 (1, 0)) w :=
    contDiffAt_snd.fst.clm_apply contDiffAt_const
  have ht : ContDiffAt ℝ ∞ (fun v : PrincipalJetInput => v.2.1 (0, 1)) w :=
    contDiffAt_snd.fst.clm_apply contDiffAt_const
  have hdet := (hr.fst.mul ht.snd).sub (hr.snd.mul ht.fst)
  have hheight : ContDiffAt ℝ ∞ (fun v : PrincipalJetInput => v.2.2) w :=
    contDiffAt_snd.snd
  have hscale : ContDiffAt ℝ ∞
      (fun v : PrincipalJetInput => 1 / (v.2.2 ^ 2 *
        |(v.2.1 (1, 0)).1 * (v.2.1 (0, 1)).2 -
          (v.2.1 (1, 0)).2 * (v.2.1 (0, 1)).1|)) w :=
    contDiffAt_const.fun_div ((hheight.pow 2).mul (hdet.abs hJ))
      (mul_ne_zero (pow_ne_zero 2 hh) (abs_ne_zero.mpr hJ))
  have hAa : ContDiffAt ℝ ∞ (fun v : PrincipalJetInput => A.a v.1) w :=
    ha.comp w contDiffAt_fst
  have hAb : ContDiffAt ℝ ∞ (fun v : PrincipalJetInput => A.b v.1) w :=
    hb.comp w contDiffAt_fst
  have hAc : ContDiffAt ℝ ∞ (fun v : PrincipalJetInput => A.c v.1) w :=
    hc.comp w contDiffAt_fst
  have htwo : ContDiffAt ℝ ∞ (fun _ : PrincipalJetInput => (2 : ℝ)) w :=
    contDiffAt_const
  unfold principalJetFormula
  split_ifs
  · exact hscale.mul (((hAa.mul (ht.snd.pow 2)).add
      (((htwo.mul hAb).mul ht.snd).mul ht.fst.neg)).add
        (hAc.mul (ht.fst.neg.pow 2)))
  · exact hscale.mul ((((hAa.mul ht.snd).mul hr.snd.neg).add
      (hAb.mul ((ht.snd.mul hr.fst).add (ht.fst.neg.mul hr.snd.neg)))).add
        ((hAc.mul ht.fst.neg).mul hr.fst))
  · exact hscale.mul (((hAa.mul (hr.snd.neg.pow 2)).add
      (((htwo.mul hAb).mul hr.snd.neg).mul hr.fst)).add
        (hAc.mul (hr.fst.pow 2)))

/-- Coordinate jets and height jets, not transformed coefficient jets,
are the inputs. All smoothness assumptions are ordinary at the actual
point, including the transported physical coefficient point. -/
theorem finiteFullJetMatch_adjugatePrincipal
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    {h q : PolarPoint → ℝ} {p : PolarPoint} {n : ℕ}
    (hFG : FiniteFullJetMatch (n + 1) p F G)
    (hhq : FiniteFullJetMatch n p h q)
    (ha : ContDiffAt ℝ ∞ A.a (F p)) (hb : ContDiffAt ℝ ∞ A.b (F p))
    (hc : ContDiffAt ℝ ∞ A.c (F p))
    (hh : h p ≠ 0) (hJ : planeJacobian F p ≠ 0) (i : Fin 3) :
    FiniteFullJetMatch n p
      (canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients A F h))
      (canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients A G q)) := by
  have hinput := (hFG.mono (Nat.le_succ n)).prodMk (hFG.fderiv.prodMk hhq)
  have houter : ContDiffAt ℝ ∞ (principalJetFormula A i)
      (F p, (fderiv ℝ F p, h p)) :=
    contDiffAt_principalJetFormula (A := A)
      (w := (F p, (fderiv ℝ F p, h p))) ha hb hc hh hJ i
  have he (T : PolarPoint → PolarPoint) (v : PolarPoint → ℝ) :
      canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients A T v) =
        principalJetFormula A i ∘ (fun x => (T x, (fderiv ℝ T x, v x))) := by
    funext x
    simp only [Function.comp_def, principalJetFormula, canonicalCoefficientComponent,
      ite_apply, adjugateCoordinatePrincipalCoefficients, coefficientQuadratic, planeJacobian]
  rw [he F h, he G q]
  exact hinput.comp houter

end ContinuousFlexibility.Analysis
