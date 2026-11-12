import ContinuousFlexibility.Analysis.N07bReferenceAngularBound

/-!
# Actual reference PDE and its current angular derivatives

The twenty-one starting coefficients come from the actual reference radial
operator and inverse transition. Applying the current inverse angular
vector gives exactly the coefficients estimated in `ReferenceAngularBound`.
The finite expansion is proved here, rather than assumed as a forcing
identity. Every resulting material jet has order at most `j + 2`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint ContinuousFlexibility.Radial
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual three reference multipliers are smooth wherever the
reference radial coordinate is nonzero. -/
theorem n07bReferenceSeedMultiplier_contDiffOn
    {U : Set PolarPoint} (hU : IsOpen U)
    {Θ : PolarPoint → PolarPoint} (hΘ : ContDiffOn ℝ ∞ Θ U)
    {B : PolarPoint → ℝ} (hB : ContDiffOn ℝ ∞ B U)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hne : ∀ x ∈ U, (Θ x).1 ≠ 0) (k : Fin 3) :
    ContDiffOn ℝ ∞ (n07bReferenceSeedMultiplier w Θ B k) U := by
  intro x hx
  have hΘx := hΘ.contDiffAt (hU.mem_nhds hx)
  have hBx := hB.contDiffAt (hU.mem_nhds hx)
  have hwx : ContDiffAt ℝ ∞ (fun y => w (Θ y).1) x :=
    hw.contDiffAt.comp x hΘx.fst
  have hdwx : ContDiffAt ℝ ∞ (fun y => deriv w (Θ y).1) x :=
    (contDiff_infty_iff_deriv.mp hw).2.contDiffAt.comp x hΘx.fst
  fin_cases k
  · change ContDiffWithinAt ℝ ∞ (fun y => B y * deriv w (Θ y).1) U x
    exact (hBx.mul hdwx).contDiffWithinAt
  · change ContDiffWithinAt ℝ ∞ (fun y => B y * w (Θ y).1) U x
    exact (hBx.mul hwx).contDiffWithinAt
  · change ContDiffWithinAt ℝ ∞ (fun y => B y * (deriv w (Θ y).1 / (Θ y).1)) U x
    exact (hBx.mul (hdwx.div hΘx.fst (hne x hx))).contDiffWithinAt

/-- The actual reference PDE has the full finite expansion whose
normalized coefficients satisfy the primitive geometric estimates.
All coordinate identities are genuine inverse-transition hypotheses;
there is no assumed identity for the forcing or its derivatives. -/
theorem n07b_referencePDE_currentAngular_material_expansion
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {V : Set PolarPoint} (hV : IsOpen V)
    {τ Θ : PolarPoint → PolarPoint}
    (hτ : ContDiffOn ℝ ∞ τ V)
    (hΘ : ContDiffOn ℝ ∞ Θ (physicalPieceOpen S K z m))
    (hτmap : MapsTo τ V (physicalPieceOpen S K z m))
    (hΘmap : MapsTo Θ (physicalPieceOpen S K z m) V)
    (hinv : ∀ y ∈ V, Θ (τ y) = y)
    (hleft : ∀ x ∈ physicalPieceOpen S K z m, τ (Θ x) = x)
    (β : ℝ) {c f B : PolarPoint → ℝ}
    (hc : ContDiffOn ℝ ∞ c (physicalPieceOpen S K z m))
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hB : ContDiffOn ℝ ∞ B (physicalPieceOpen S K z m))
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hne : ∀ x ∈ physicalPieceOpen S K z m, (Θ x).1 ≠ 0)
    (j : ℕ) {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    n07bDirectionIterate (fun _ => n07bInverseAngleVector (K.chart z m))
      (fun y => B y * radialPDE w (fun r θ => c (τ (r, θ)) * f (τ (r, θ)))
        (Θ y).1 (Θ y).2) j x =
      T.H x.1 ^ β * ∑ i : n07bReferenceMaterialSeed × n07bAngularChainIndex j,
        n07bReferenceAngularCoefficient T K z m β
          (n07bReferenceDirection τ Θ (1, 0)) (n07bReferenceDirection τ Θ (0, 1))
          c (n07bReferenceSeedMultiplier w Θ B) j i x *
          mixedDerivative
            (n07bReferenceSeedRadial i.1 + n07bAngularChainRadial j i.2)
            (n07bReferenceSeedAngular i.1 + n07bAngularChainAngular j i.2)
            (materialPullback T β f) (n07bMaterialChart T x) := by
  have hU := (hK.domains z hz hs m).1
  have hcore := (hK.domains z hz hs m).2.2.1
  have hXr := n07bReferenceDirection_contDiffOn hU hV hτ hΘ hΘmap (1, 0)
  have hXθ := n07bReferenceDirection_contDiffOn hU hV hτ hΘ hΘmap (0, 1)
  have hA := n07bReferenceSeedMultiplier_contDiffOn hU hΘ hB hw hne
  have hseed : ∀ i : n07bReferenceMaterialSeed,
      ContDiffOn ℝ ∞ (n07bReferenceSeedCoefficient T β
        (n07bReferenceDirection τ Θ (1, 0)) (n07bReferenceDirection τ Θ (0, 1))
        c (n07bReferenceSeedMultiplier w Θ B) i) (physicalPieceOpen S K z m) := by
    intro i y hy
    exact (n07bReferenceSeedCoefficient_contDiffAt hT (hcore hy).1 β
      (hXr.contDiffAt (hU.mem_nhds hy)) (hXθ.contDiffAt (hU.mem_nhds hy))
      (hc.contDiffAt (hU.mem_nhds hy)) (fun k => (hA k).contDiffAt (hU.mem_nhds hy))
      i).contDiffWithinAt
  have hangle : ContDiffOn ℝ ∞ (n07bInverseAngleVector (K.chart z m))
      (physicalPieceOpen S K z m) := by
    intro y hy
    have hclosed := (hK.boundary z hz hs m).2.2.2.2.1 y (subset_closure hy)
    exact (n07b_contDiffAt_inverseAngleVector hclosed.1 hclosed.2.2.1).contDiffWithinAt
  apply n07b_directionChain_of_finite_material_expansion hT hU hcore
    (fun _ => n07bInverseAngleVector (K.chart z m)) (fun _ => hangle) β
    n07bReferenceSeedRadial n07bReferenceSeedAngular hseed
    (contDiff_materialPullback hT hf) (j := j) (hx := hx)
  intro y hy
  exact n07b_referencePDE_material_seed_expansion hT hU hV hcore
    hτ hΘ hτmap hΘmap hinv hleft β hc hf B hy
    (hw.differentiable (by simp) (Θ y).1)

end ContinuousFlexibility.Analysis
