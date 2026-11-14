module

public import ContinuousFlexibility.Analysis.BoundaryTaylorDensity
public import ContinuousFlexibility.Analysis.BoundaryJetClosure
public import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction

/-!
# Actual principal remainder after boundary Taylor matching

The physical remainder is the transformed density minus the common
canonical normal form evaluated at the new chart. A genuine normal-form
equation on the adjacent open root region determines its boundary jets.
The Taylor chart and logarithmic height construction then force the
remainder jets to vanish. No zero jets of the constructed density are
assumed, and one component selector covers all three coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem contDiffOn_principalDensity_component
    {U : Set PolarPoint} (hU : IsOpen U) {A : SymmetricCoefficients}
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    (hAa : ContDiffOn ℝ ∞ A.a U) (hAb : ContDiffOn ℝ ∞ A.b U)
    (hAc : ContDiffOn ℝ ∞ A.c U) (hF : ContDiffOn ℝ ∞ F U)
    (hh : ContDiffOn ℝ ∞ h U)
    (hJ : ∀ p ∈ U, planeJacobian F p ≠ 0) (i : Fin 3) :
    ContDiffOn ℝ ∞
      (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h)) U := by
  intro p hp
  have hs := contDiffAt_coordinatePrincipalDensity
    (hAa.contDiffAt (hU.mem_nhds hp)) (hAb.contDiffAt (hU.mem_nhds hp))
    (hAc.contDiffAt (hU.mem_nhds hp)) (hF.contDiffAt (hU.mem_nhds hp))
    (hh.contDiffAt (hU.mem_nhds hp)) (hJ p hp)
  have hc : ContDiffAt ℝ ∞
      (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h)) p := by
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hs.1
    · exact hs.2.1
    · exact hs.2.2
  exact hc.contDiffWithinAt

/-- The normal-form field is evaluated at the corrected chart, rather
than at the unchanged physical point. -/
def boundaryTaylorPrincipalRemainder (A : SymmetricCoefficients) (n : ℕ)
    (c d : ℝ) (Fref F : PolarPoint → PolarPoint) (href h : PolarPoint → ℝ)
    (N : ℝ → ℝ) (i : Fin 3) (p : PolarPoint) : ℝ :=
  canonicalCoefficientComponent i (coordinatePrincipalDensity A
    (boundaryTaylorChart (n + 1) c d Fref F) (boundaryTaylorHeight n c d href h)) p -
      N ((boundaryTaylorChart (n + 1) c d Fref F p).1)

/-- Actual root normal form, coordinate degree n+1 and logarithmic height
degree n give a smooth physical remainder with zero radial jets through
n. Both endpoints use the same statement. The two nonzero-Jacobian inputs
are explicit geometric conditions, not coefficient-jet assumptions. -/
theorem boundaryTaylorPrincipalRemainder_smooth_zeroJets
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {A : SymmetricCoefficients} {Fref F : PolarPoint → PolarPoint}
    {href h : PolarPoint → ℝ}
    (hAa : ContDiffOn ℝ ∞ A.a U) (hAb : ContDiffOn ℝ ∞ A.b U)
    (hAc : ContDiffOn ℝ ∞ A.c U)
    (hFref : ContDiffOn ℝ ∞ Fref U) (hF : ContDiffOn ℝ ∞ F U)
    (hRef : ContDiffOn ℝ ∞ href U) (hh : ContDiffOn ℝ ∞ h U)
    (hRefPos : ∀ p ∈ U, 0 < href p) (hPos : ∀ p ∈ U, 0 < h p)
    {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (side : Bool) (i : Fin 3) {N : ℝ → ℝ} (hN : ContDiff ℝ ∞ N)
    (hJ : ∀ p ∈ U, planeJacobian F p ≠ 0)
    (hJnew : ∀ p ∈ U,
      planeJacobian (boundaryTaylorChart (n + 1) c d Fref F) p ≠ 0)
    (hroot : EqOn (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h))
      (fun p => N ((F p).1)) V)
    (hclosure : ∀ θ : ℝ, (if side then d else c, θ) ∈ closure V) :
    ContDiffOn ℝ ∞ (boundaryTaylorPrincipalRemainder A n c d Fref F href h N i) U ∧
      ∀ k ≤ n, ∀ θ : ℝ,
        radialBoundaryJet (boundaryTaylorPrincipalRemainder A n c d Fref F href h N i)
          (if side then d else c) k θ = 0 := by
  let Fnew := boundaryTaylorChart (n + 1) c d Fref F
  let hnew := boundaryTaylorHeight n c d href h
  let ρ := canonicalCoefficientComponent i (coordinatePrincipalDensity A Fnew hnew)
  let ρ₀ := canonicalCoefficientComponent i (coordinatePrincipalDensity A F h)
  let x : ℝ := if side then d else c
  have hx : ∀ θ : ℝ, (x, θ) ∈ U := by
    cases side with
    | false => exact hc
    | true => exact hd
  have hFn : ContDiffOn ℝ ∞ Fnew U :=
    contDiffOn_boundaryTaylorChart hU hFref hF hc hd (n + 1) hFref
  have hhn : ContDiffOn ℝ ∞ hnew U :=
    contDiffOn_boundaryTaylorHeight hU hRef hh hRefPos hPos hc hd n hRef
  have hρ : ContDiffOn ℝ ∞ ρ U :=
    contDiffOn_principalDensity_component hU hAa hAb hAc hFn hhn hJnew i
  have hρ₀ : ContDiffOn ℝ ∞ ρ₀ U :=
    contDiffOn_principalDensity_component hU hAa hAb hAc hF hh hJ i
  have hNF : ContDiffOn ℝ ∞ (fun p => N ((F p).1)) U :=
    hN.fun_comp_contDiffOn hF.fst
  have hNFn : ContDiffOn ℝ ∞ (fun p => N ((Fnew p).1)) U :=
    hN.fun_comp_contDiffOn hFn.fst
  have hmatch : ∀ k ≤ n, ∀ θ : ℝ,
      radialBoundaryJet ρ x k θ = radialBoundaryJet ρ₀ x k θ := by
    intro k hk θ
    have hparts := radialBoundaryJets_boundaryTaylorDensity_eq
      hU hAa hAb hAc hFref hF hRef hh hRefPos hPos hcd hc hd
      n side θ (hJ (x, θ) (hx θ)) k hk
    dsimp only [ρ, ρ₀]
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hparts.1
    · exact hparts.2.1
    · exact hparts.2.2
  have hcoord : ∀ k ≤ n, ∀ θ : ℝ,
      radialBoundaryJet (fun p => (Fnew p).1) x k θ =
        radialBoundaryJet (fun p => (F p).1) x k θ := by
    intro k hk θ
    exact iteratedDeriv_boundaryTaylorPerturbation_eq hU hFref.fst hF.fst
      hcd hc hd (n + 1) side (hk.trans (Nat.le_succ n)) θ
  refine ⟨hρ.sub hNFn, ?_⟩
  intro k hk θ
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  have hψ : ContDiffAt ℝ ∞ (fun r => (Fnew (r, θ)).1) x :=
    ContDiffAt.comp (f := fun r : ℝ => (r, θ))
      (g := fun p : PolarPoint => (Fnew p).1) x
      (hFn.fst.contDiffAt (hU.mem_nhds (hx θ))) hline
  have hψ₀ : ContDiffAt ℝ ∞ (fun r => (F (r, θ)).1) x :=
    ContDiffAt.comp (f := fun r : ℝ => (r, θ))
      (g := fun p : PolarPoint => (F p).1) x
      (hF.fst.contDiffAt (hU.mem_nhds (hx θ))) hline
  have hcomp : radialBoundaryJet (fun p => N ((Fnew p).1)) x k θ =
      radialBoundaryJet (fun p => N ((F p).1)) x k θ := by
    simpa only [radialBoundaryJet, Function.comp_def] using
      iteratedDeriv_vcomp_eq_of_finiteJet_eq hψ hψ₀ hN.contDiffAt
        (fun j hj => hcoord j hj θ) hk
  have hnormal : radialBoundaryJet ρ₀ x k θ =
      radialBoundaryJet (fun p => N ((F p).1)) x k θ := by
    simpa only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero] using
      mixedDerivative_eq_at_closure_of_contDiffAt hV
        (hρ₀.contDiffAt (hU.mem_nhds (hx θ)))
        (hNF.contDiffAt (hU.mem_nhds (hx θ))) hroot (hclosure θ) k 0
  have hsρ : ContDiffAt ℝ ∞ (fun r => ρ (r, θ)) x :=
    (hρ.contDiffAt (hU.mem_nhds (hx θ))).comp x hline
  have hsN : ContDiffAt ℝ ∞ (fun r => N ((Fnew (r, θ)).1)) x :=
    ContDiffAt.comp (f := fun r : ℝ => (r, θ))
      (g := fun p : PolarPoint => N ((Fnew p).1)) x
      (hNFn.contDiffAt (hU.mem_nhds (hx θ))) hline
  change iteratedDeriv k (fun r => ρ (r, θ) - N ((Fnew (r, θ)).1)) x = 0
  rw [iteratedDeriv_fun_sub
    (hsρ.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hsN.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))]
  change radialBoundaryJet ρ x k θ -
    radialBoundaryJet (fun p => N ((Fnew p).1)) x k θ = 0
  rw [hmatch k hk θ, hcomp, hnormal, sub_self]

end ContinuousFlexibility.Analysis

