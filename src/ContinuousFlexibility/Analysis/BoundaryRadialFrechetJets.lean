module

public import ContinuousFlexibility.Analysis.BoundaryMixedJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Finite radial matching preserves the actual boundary Fréchet jets

Radial matching is an equality of functions of the angle. The existing
zero-jet theorem for the difference therefore identifies the full
Fréchet jets, with no factor or loss in derivative order. Both fields
are smooth on the given genuine open collar.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem iteratedFDeriv_eq_of_radialBoundaryJets_eq
    {U : Set PolarPoint} (hU : IsOpen U) {F G : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (c : ℝ) (hc : ∀ θ, (c, θ) ∈ U) {n : ℕ}
    (hjet : ∀ j ≤ n, ∀ θ, radialBoundaryJet F c j θ = radialBoundaryJet G c j θ)
    {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedFDeriv ℝ k F (c, θ) = iteratedFDeriv ℝ k G (c, θ) := by
  let H : PolarPoint → ℝ := fun p => F p - G p
  have hH : ContDiffOn ℝ ∞ H U := hF.sub hG
  have hzero (j : ℕ) (hj : j ≤ n) (η : ℝ) :
      radialBoundaryJet H c j η = 0 := by
    have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, η)) c :=
      contDiffAt_id.prodMk contDiffAt_const
    have hFs : ContDiffAt ℝ ∞ (fun r : ℝ => F (r, η)) c :=
      (hF.contDiffAt (hU.mem_nhds (hc η))).comp c hline
    have hGs : ContDiffAt ℝ ∞ (fun r : ℝ => G (r, η)) c :=
      (hG.contDiffAt (hU.mem_nhds (hc η))).comp c hline
    change iteratedDeriv j (fun r => F (r, η) - G (r, η)) c = 0
    rw [iteratedDeriv_fun_sub
      (hFs.of_le (show (j : ℕ∞ω) ≤ ∞ by simp))
      (hGs.of_le (show (j : ℕ∞ω) ≤ ∞ by simp))]
    exact sub_eq_zero.mpr (hjet j hj η)
  have hfull := iteratedFDeriv_eq_zero_of_radialBoundaryJets_zero
    hU hH c hc hzero hk θ
  change iteratedFDeriv ℝ k (F - G) (c, θ) = 0 at hfull
  rw [iteratedFDeriv_sub_apply
    ((hF.contDiffAt (hU.mem_nhds (hc θ))).of_le (by simp : (k : ℕ∞ω) ≤ ∞))
    ((hG.contDiffAt (hU.mem_nhds (hc θ))).of_le (by simp : (k : ℕ∞ω) ≤ ∞))] at hfull
  exact sub_eq_zero.mp hfull

/-- The finite forward-jet input for the actual angular inverse can be
taken from the original root angle, after its radial Taylor matching. -/
theorem norm_iteratedFDeriv_le_of_radialBoundaryJets_eq
    {U : Set PolarPoint} (hU : IsOpen U) {F G : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (c : ℝ) (hc : ∀ θ, (c, θ) ∈ U) {n : ℕ}
    (hjet : ∀ j ≤ n, ∀ θ, radialBoundaryJet F c j θ = radialBoundaryJet G c j θ)
    {k : ℕ} (hk : k ≤ n) {M : ℝ} {θ : ℝ}
    (hbound : ‖iteratedFDeriv ℝ k G (c, θ)‖ ≤ M) :
    ‖iteratedFDeriv ℝ k F (c, θ)‖ ≤ M := by
  rw [iteratedFDeriv_eq_of_radialBoundaryJets_eq hU hF hG c hc hjet hk θ]
  exact hbound

end ContinuousFlexibility.Analysis
