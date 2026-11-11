import ContinuousFlexibility.Analysis.PositiveConformalDensityJets
import ContinuousFlexibility.Analysis.CoordinateOperatorConstruction

/-!
# Finite conformal data give the actual canonical boundary jets

The new chart and height need only match the constructed finite coordinate
polynomial and the actual fourth-root height. Their boundary Jacobian is
proved positive from first-jet matching. The full principal-density jet
comparison then gives physical vanishing, and the genuine smooth inverse
transports it to ordinary canonical radial jets. No density zero jets or
Jacobian estimate for the new chart are hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem conformal_matching_partials
    {f g : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (c : ℝ) {n : ℕ}
    (hjet : ∀ j ≤ n + 1, ∀ θ, radialBoundaryJet f c j θ = radialBoundaryJet g c j θ)
    (θ : ℝ) :
    radialPartial f (c, θ) = radialPartial g (c, θ) ∧
      angularPartial f (c, θ) = angularPartial g (c, θ) := by
  have hr := hjet 1 (by omega) θ
  simp only [radialBoundaryJet, iteratedDeriv_one] at hr
  rw [deriv_cylinder_radial_slice (hf.differentiable (by simp)) c θ,
    deriv_cylinder_radial_slice (hg.differentiable (by simp)) c θ] at hr
  have he : (fun η => f (c, η)) = fun η => g (c, η) := by
    funext η
    simpa only [radialBoundaryJet, iteratedDeriv_zero] using hjet 0 (by omega) η
  have ht := congrArg (fun u : ℝ → ℝ => deriv u θ) he
  rw [deriv_cylinder_angular_slice (hf.differentiable (by simp)) c θ,
    deriv_cylinder_angular_slice (hg.differentiable (by simp)) c θ] at ht
  exact ⟨hr, ht⟩

private theorem conformal_matching_jacobian
    {F P : PolarPoint → PolarPoint} (hF : ContDiff ℝ ∞ F) (hP : ContDiff ℝ ∞ P)
    (c : ℝ) {n : ℕ}
    (hfst : ∀ j ≤ n + 1, ∀ θ, radialBoundaryJet (fun q => (F q).1) c j θ =
      radialBoundaryJet (fun q => (P q).1) c j θ)
    (hsnd : ∀ j ≤ n + 1, ∀ θ, radialBoundaryJet (fun q => (F q).2) c j θ =
      radialBoundaryJet (fun q => (P q).2) c j θ) (θ : ℝ) :
    planeJacobian F (c, θ) = planeJacobian P (c, θ) := by
  have h₁ := conformal_matching_partials hF.fst hP.fst c hfst θ
  have h₂ := conformal_matching_partials hF.snd hP.snd c hsnd θ
  have hDF := (((hF.fst.differentiable (by simp) (c, θ)).hasFDerivAt).prodMk
    (hF.snd.differentiable (by simp) (c, θ)).hasFDerivAt).fderiv
  have hDP := (((hP.fst.differentiable (by simp) (c, θ)).hasFDerivAt).prodMk
    (hP.snd.differentiable (by simp) (c, θ)).hasFDerivAt).fderiv
  change planeJacobian (fun q => ((F q).1, (F q).2)) (c, θ) =
    planeJacobian (fun q => ((P q).1, (P q).2)) (c, θ)
  simp only [planeJacobian, hDF, hDP, ContinuousLinearMap.prod_apply]
  change radialPartial (fun q => (F q).1) (c, θ) *
      angularPartial (fun q => (F q).2) (c, θ) -
      radialPartial (fun q => (F q).2) (c, θ) *
        angularPartial (fun q => (F q).1) (c, θ) =
    radialPartial (fun q => (P q).1) (c, θ) *
      angularPartial (fun q => (P q).2) (c, θ) -
      radialPartial (fun q => (P q).2) (c, θ) *
        angularPartial (fun q => (P q).1) (c, θ)
  rw [h₁.1, h₁.2, h₂.1, h₂.2]

private theorem conformal_matching_sub_one
    {f g : PolarPoint → ℝ} {c θ : ℝ}
    (hf : ContDiffAt ℝ ∞ f (c, θ)) (hg : ContDiffAt ℝ ∞ g (c, θ)) (k : ℕ)
    (hk : radialBoundaryJet f c k θ = radialBoundaryJet g c k θ) :
    radialBoundaryJet (fun p => f p - 1) c k θ =
      radialBoundaryJet (fun p => g p - 1) c k θ := by
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hfs := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ)) (g := f) c hf hline
  have hgs := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ)) (g := g) c hg hline
  have hone : ContDiffAt ℝ (k : ℕ∞ω) (fun _ : ℝ => (1 : ℝ)) c := contDiffAt_const
  change iteratedDeriv k (fun r => f (r, θ)) c =
    iteratedDeriv k (fun r => g (r, θ)) c at hk
  change iteratedDeriv k (fun r => f (r, θ) - 1) c =
    iteratedDeriv k (fun r => g (r, θ) - 1) c
  rw [iteratedDeriv_fun_sub (hfs.of_le (by simp)) hone,
    iteratedDeriv_fun_sub (hgs.of_le (by simp)) hone, hk]

/-- Degree n+1 coordinate matching and degree n height matching imply
the actual canonical unit-density jets through n. The open physical
smoothness domain is explicit; no common neighborhood is inferred from
pointwise infinite differentiability. The inverse is the actual global
inverse produced by the positive fiber construction. -/
theorem positiveConformal_matchingChart_canonicalJets
    {U : Set PolarPoint} (hU : IsOpen U) {A : SymmetricCoefficients}
    (hAa : ContDiffOn ℝ ∞ A.a U) (hAb : ContDiffOn ℝ ∞ A.b U)
    (hAc : ContDiffOn ℝ ∞ A.c U)
    (ha0 : ∀ p ∈ U, 0 < A.a p)
    (hdet : ∀ p ∈ U, 0 < A.a p * A.c p - A.b p ^ 2)
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hh : ContDiff ℝ ∞ h)
    (hGF : Function.LeftInverse G F) (c v : ℝ) (hc : ∀ θ, (c, θ) ∈ U) (n : ℕ)
    (hfst : ∀ j ≤ n + 1, ∀ θ,
      radialBoundaryJet (fun q => (F q).1) c j θ =
        radialBoundaryJet (positiveConformalBoundaryPolynomial (n + 1) c v
          (positiveConformalSpeed A) (positiveConformalShear A) false) c j θ)
    (hsnd : ∀ j ≤ n + 1, ∀ θ,
      radialBoundaryJet (fun q => (F q).2) c j θ =
        radialBoundaryJet (positiveConformalBoundaryPolynomial (n + 1) c v
          (positiveConformalSpeed A) (positiveConformalShear A) true) c j θ)
    (hheight : ∀ j ≤ n, ∀ θ,
      radialBoundaryJet h c j θ = radialBoundaryJet (positiveConformalHeight A) c j θ) :
    ∀ θ, F (c, θ) = (v, θ) ∧ 0 < planeJacobian F (c, θ) ∧
      ∀ k ≤ n,
        radialBoundaryJet
          (fun p => (inverseChartPrincipalCoefficients A F G h).a p - 1) v k θ = 0 ∧
        radialBoundaryJet (inverseChartPrincipalCoefficients A F G h).b v k θ = 0 ∧
        radialBoundaryJet
          (fun p => (inverseChartPrincipalCoefficients A F G h).c p - 1) v k θ = 0 := by
  let X := positiveConformalBoundaryPolynomial (n + 1) c v
    (positiveConformalSpeed A) (positiveConformalShear A)
  let P : PolarPoint → PolarPoint := fun p => (X false p, X true p)
  let B := coordinatePrincipalDensity A F h
  have hpoly := positiveConformalBoundaryPolynomial_density_jets
    (fun θ => hAa.contDiffAt (hU.mem_nhds (hc θ)))
    (fun θ => hAb.contDiffAt (hU.mem_nhds (hc θ)))
    (fun θ => hAc.contDiffAt (hU.mem_nhds (hc θ)))
    (fun θ => ha0 (c, θ) (hc θ)) (fun θ => hdet (c, θ) (hc θ)) n v
  have hP : ContDiff ℝ ∞ P := hpoly.1
  have hJ (θ : ℝ) : 0 < planeJacobian F (c, θ) := by
    rw [conformal_matching_jacobian hF hP c hfst hsnd θ]
    exact (hpoly.2 θ).2.1
  have hvalue (θ : ℝ) : F (c, θ) = (v, θ) := by
    have h₁ := hfst 0 (Nat.zero_le _) θ
    have h₂ := hsnd 0 (Nat.zero_le _) θ
    simp only [radialBoundaryJet, iteratedDeriv_zero] at h₁ h₂
    exact (Prod.ext h₁ h₂).trans (hpoly.2 θ).1
  have hH : ContDiffOn ℝ ∞ (positiveConformalHeight A) U := by
    intro p hp
    exact ((contDiffAt_positiveConformalFields
      (hAa.contDiffAt (hU.mem_nhds hp)) (hAb.contDiffAt (hU.mem_nhds hp))
      (hAc.contDiffAt (hU.mem_nhds hp)) (ha0 p hp) (hdet p hp)).2.2).contDiffWithinAt
  have hmatch (θ : ℝ) := radialBoundaryJets_coordinatePrincipalDensity_eq
    hU hAa hAb hAc hP.contDiffOn hF.contDiffOn hH hh.contDiffOn c hc
    (fun j hj η => (hfst j hj η).symm) (fun j hj η => (hsnd j hj η).symm)
    (fun j hj η => (hheight j hj η).symm) θ (hpoly.2 θ).2.1.ne'
  let V : Set PolarPoint := U ∩ {p | planeJacobian F p ≠ 0}
  have hJcont : Continuous (planeJacobian F) :=
    continuous_iff_continuousAt.mpr fun p =>
      (contDiffAt_planeJacobian (hF.contDiffAt (x := p))).continuousAt
  have hV : IsOpen V := hU.inter (isOpen_ne_fun hJcont continuous_const)
  have hcV (θ : ℝ) : (c, θ) ∈ V := ⟨hc θ, (hJ θ).ne'⟩
  have hB : ContDiffOn ℝ ∞ B.a V ∧ ContDiffOn ℝ ∞ B.b V ∧ ContDiffOn ℝ ∞ B.c V := by
    have hs (p : PolarPoint) (hp : p ∈ V) := contDiffAt_coordinatePrincipalDensity
      (hAa.contDiffAt (hU.mem_nhds hp.1)) (hAb.contDiffAt (hU.mem_nhds hp.1))
      (hAc.contDiffAt (hU.mem_nhds hp.1)) hF.contDiffAt hh.contDiffAt hp.2
    exact ⟨fun p hp => (hs p hp).1.contDiffWithinAt,
      fun p hp => (hs p hp).2.1.contDiffWithinAt,
      fun p hp => (hs p hp).2.2.contDiffWithinAt⟩
  have hphysical (j : ℕ) (hj : j ≤ n) (θ : ℝ) :
      radialBoundaryJet (fun p => B.a p - 1) c j θ = 0 ∧
      radialBoundaryJet B.b c j θ = 0 ∧
      radialBoundaryJet (fun p => B.c p - 1) c j θ = 0 := by
    have hp := contDiffAt_coordinatePrincipalDensity
      (hAa.contDiffAt (hU.mem_nhds (hc θ))) (hAb.contDiffAt (hU.mem_nhds (hc θ)))
      (hAc.contDiffAt (hU.mem_nhds (hc θ))) hP.contDiffAt
      (hH.contDiffAt (hU.mem_nhds (hc θ))) (hpoly.2 θ).2.1.ne'
    have hm := hmatch θ j hj
    have hz := (hpoly.2 θ).2.2.2.2 j hj
    exact ⟨(conformal_matching_sub_one hp.1
        (hB.1.contDiffAt (hV.mem_nhds (hcV θ))) j hm.1).symm.trans hz.1,
      hm.2.1.symm.trans hz.2.1,
      (conformal_matching_sub_one hp.2.2
        (hB.2.2.contDiffAt (hV.mem_nhds (hcV θ))) j hm.2.2).symm.trans hz.2.2⟩
  intro θ
  refine ⟨hvalue θ, hJ θ, ?_⟩
  have hGvalue : G (v, θ) = (c, θ) := by
    rw [← hvalue θ]
    exact hGF (c, θ)
  have hcurve : ContDiffAt ℝ ∞ (fun r : ℝ => G (r, θ)) v :=
    ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ)) (g := G) v hG.contDiffAt
      (contDiffAt_id.prodMk contDiffAt_const)
  intro k hk
  have ha := iteratedDeriv_comp_eq_zero_of_radialBoundaryJets_zero hV
    (hB.1.sub contDiffOn_const) c hcV
    (fun j hj η => (hphysical j hj η).1) hcurve hGvalue hk
  have hb := iteratedDeriv_comp_eq_zero_of_radialBoundaryJets_zero hV hB.2.1 c hcV
    (fun j hj η => (hphysical j hj η).2.1) hcurve hGvalue hk
  have hd := iteratedDeriv_comp_eq_zero_of_radialBoundaryJets_zero hV
    (hB.2.2.sub contDiffOn_const) c hcV
    (fun j hj η => (hphysical j hj η).2.2) hcurve hGvalue hk
  simpa only [radialBoundaryJet, inverseChartPrincipalCoefficients, Function.comp_def, B]
    using And.intro ha (And.intro hb hd)

end ContinuousFlexibility.Analysis
