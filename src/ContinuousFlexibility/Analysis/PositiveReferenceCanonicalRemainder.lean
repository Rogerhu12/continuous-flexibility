module

public import ContinuousFlexibility.Analysis.PositiveReferenceCylinder
public import ContinuousFlexibility.Analysis.CanonicalEndpointInverse

/-!
# The actual canonical reference remainder through an endpoint

The scalar interpolation has a genuine global smooth inverse. Its
canonical density is therefore defined through that inverse, including
at the endpoint. Local density smoothness follows on the open inverse
image of the physical collar. Matching endpoint germs and an actual
one-sided root normal form force its finite boundary jets to vanish.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveReferenceCanonicalRemainder (A : SymmetricCoefficients)
    (Y H N : ℝ → ℝ) (i : Fin 3) (p : PolarPoint) : ℝ :=
  canonicalCoefficientComponent i
    (coordinatePrincipalDensity A (positiveReferenceCylinderChart Y)
      (fun q => H q.1)) (positiveReferenceCylinderInverse Y p) - N p.1

/-- All regularity and invertibility inputs for Y and H are outputs of
the proved scalar interpolation factory. Only the original one-sided
root equation is used to obtain vanishing; no zero jet is an input. -/
theorem positiveReferenceCanonicalRemainder_smooth_zeroJets
    {A : SymmetricCoefficients} {Y H N : ℝ → ℝ}
    {Froot : PolarPoint → PolarPoint} {hroot : PolarPoint → ℝ}
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    (hAa : ContDiffOn ℝ ∞ A.a U) (hAb : ContDiffOn ℝ ∞ A.b U)
    (hAc : ContDiffOn ℝ ∞ A.c U)
    (hY : ContDiff ℝ ∞ Y) (hYpos : ∀ r, 0 < deriv Y r)
    (hYbij : Function.Bijective Y) (hYinv : ContDiff ℝ ∞ (Function.invFun Y))
    (hH : ContDiff ℝ ∞ H) (hN : ContDiff ℝ ∞ N)
    (c : ℝ) (hc : ∀ θ : ℝ, (c, θ) ∈ U)
    (hclosure : ∀ θ : ℝ, (c, θ) ∈ closure V)
    (hFroot : ∀ θ : ℝ, ContDiffAt ℝ ∞ Froot (c, θ))
    (hhroot : ∀ θ : ℝ, ContDiffAt ℝ ∞ hroot (c, θ))
    (hJroot : ∀ θ : ℝ, planeJacobian Froot (c, θ) ≠ 0)
    (hFmatch : ∀ θ : ℝ,
      positiveReferenceCylinderChart Y =ᶠ[𝓝 (c, θ)] Froot)
    (hHmatch : ∀ θ : ℝ, (fun p : PolarPoint => H p.1) =ᶠ[𝓝 (c, θ)] hroot)
    (i : Fin 3)
    (hnormal : EqOn
      (canonicalCoefficientComponent i (coordinatePrincipalDensity A Froot hroot))
      (fun p => N ((Froot p).1)) V)
    (n : ℕ) (θ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ContDiffOn ℝ ∞ (positiveReferenceCanonicalRemainder A Y H N i)
        (Metric.ball (Y c, θ) δ) ∧
      ∀ k ≤ n,
        iteratedDeriv k
          (fun r => positiveReferenceCanonicalRemainder A Y H N i (r, θ)) (Y c) = 0 := by
  let F := positiveReferenceCylinderChart Y
  let G := positiveReferenceCylinderInverse Y
  let ρ := canonicalCoefficientComponent i
    (coordinatePrincipalDensity A F (fun p => H p.1))
  let R : PolarPoint → ℝ := fun p => ρ p - N ((F p).1)
  have hF : ContDiff ℝ ∞ F := contDiff_positiveReferenceCylinderChart hY
  have hG : ContDiff ℝ ∞ G := contDiff_positiveReferenceCylinderInverse hYinv
  have hleft : Function.LeftInverse G F := positiveReferenceCylinder_leftInverse hYbij.1
  have hright : Function.RightInverse G F := positiveReferenceCylinder_rightInverse hYbij.2
  have hR : ContDiffOn ℝ ∞ R U := by
    intro p hp
    have hJ : planeJacobian F p ≠ 0 := by
      rw [planeJacobian_positiveReferenceCylinderChart (hY.differentiable (by simp) p.1)]
      exact (hYpos p.1).ne'
    have hρ : ContDiffAt ℝ ∞ ρ p :=
      contDiffAt_coordinatePrincipalDensity_component
        (hAa.contDiffAt (hU.mem_nhds hp)) (hAb.contDiffAt (hU.mem_nhds hp))
        (hAc.contDiffAt (hU.mem_nhds hp)) hF.contDiffAt
        (hH.comp contDiff_fst).contDiffAt hJ i
    have hNF : ContDiffAt ℝ ∞ (fun q => N ((F q).1)) p :=
      hN.contDiffAt.comp p hF.contDiffAt.fst
    exact (hρ.sub hNF).contDiffWithinAt
  have hzero : ∀ j ≤ n, ∀ η : ℝ, radialBoundaryJet R c j η = 0 := by
    intro j _ η
    exact radialBoundaryJet_principalRemainder_eq_zero_of_germs
      hV (hclosure η)
      (hAa.contDiffAt (hU.mem_nhds (hc η)))
      (hAb.contDiffAt (hU.mem_nhds (hc η)))
      (hAc.contDiffAt (hU.mem_nhds (hc η)))
      (hFroot η) (hhroot η) (hJroot η) (hFmatch η) (hHmatch η) hN i hnormal j
  have he : positiveReferenceCanonicalRemainder A Y H N i =
      (fun p => R (G p)) := by
    funext p
    change ρ (G p) - N p.1 = ρ (G p) - N ((F (G p)).1)
    rw [hright p]
  let T : Set PolarPoint := G ⁻¹' U
  have hT : IsOpen T := hU.preimage hG.continuous
  have hbase : G (Y c, θ) = (c, θ) := hleft (c, θ)
  have hmem : (Y c, θ) ∈ T := by
    have hu : G (Y c, θ) ∈ U := by
      rw [hbase]
      exact hc θ
    exact hu
  have hE : ContDiffOn ℝ ∞ (positiveReferenceCanonicalRemainder A Y H N i) T := by
    rw [he]
    exact hR.comp hG.contDiffOn (fun _ hp => hp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hmem)
  refine ⟨δ, hδ, hE.mono hball, ?_⟩
  intro k hk
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) (Y c) :=
    contDiffAt_id.prodMk contDiffAt_const
  have hcurve : ContDiffAt ℝ ∞ (fun r => G (r, θ)) (Y c) :=
    hG.contDiffAt.comp (Y c) hline
  have hz := iteratedDeriv_comp_eq_zero_of_radialBoundaryJets_zero
    hU hR c hc hzero hcurve hbase hk
  simpa only [he, Function.comp_def] using hz

end ContinuousFlexibility.Analysis

