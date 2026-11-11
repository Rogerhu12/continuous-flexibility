import ContinuousFlexibility.Analysis.N08ScalarFormula
import ContinuousFlexibility.Analysis.SolveTameSubspace
import ContinuousFlexibility.Analysis.SpacesCompactHeights

/-!
# The nonlinear scalar state in the weighted scalar calculus

An actual realized metric perturbation determines the weighted scalar state
without changing the height, endpoint constant, or construction parameter.
The primitive-independence theorem identifies its decoded residual with the
nonlinear residual. Conservation places the weighted residual in the actual
source kernel, and closed-range restriction retains its smooth tame tower.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

def n08ScalarState (metric : AnnularState S → ScalarHeightSpace S)
    (z : AnnularState S × ℝ) : ScalarWeightedState S :=
  (((metric z.1, z.1.1.1), z.1.1.2), z.2)

theorem n08ScalarState_increment (metric : AnnularState S → ScalarHeightSpace S)
    (z : AnnularState S × ℝ) :
    scalarStateIncrement S (n08ScalarState metric z) = stateU S z.1 := rfl

theorem n08ScalarState_center (metric : AnnularState S → ScalarHeightSpace S)
    (href : referenceStateConditions D S C) (hmetric : metric C.referenceState = 0) :
    n08ScalarState metric (C.referenceState, 0) =
      scalarStateCenter S C.referenceState.1.1 := by
  simp only [n08ScalarState, scalarStateCenter, hmetric, href.2.1]

/-- The metric coordinate is the actual exponential profile perturbation. -/
theorem n08ScalarState_profile (metric : AnnularState S → ScalarHeightSpace S)
    {z : AnnularState S × ℝ}
    (hmetric : ∀ r θ, (S.height scalarBeta).decode (metric z.1) (r, θ) =
      Real.exp (z.1.2.1 * D.chi r + stateControlSum C z.1 r) - 1) :
    scalarStateProfile D S (n08ScalarState metric z) = stateProfile D S C z.1 := by
  funext r
  have hm : (fun θ => (S.height scalarBeta).decode (metric z.1) (r, θ)) =
      fun _ : ℝ => Real.exp (z.1.2.1 * D.chi r + stateControlSum C z.1 r) - 1 :=
    funext (hmetric r)
  change D.w r * (1 + angularMean (fun θ =>
    (S.height scalarBeta).decode (metric z.1) (r, θ))) = _
  rw [hm, spaces_angularMean_const]
  simp only [stateProfile, stateControlSum]
  ring

/-- The S04 primitive and the nonlinear primitive yield exactly the same
residual, for every point and including the removable value of q. -/
theorem n08ScalarState_residual (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (metric : AnnularState S → ScalarHeightSpace S) (z : AnnularState S × ℝ)
    (hprofile : scalarStateProfile D S (n08ScalarState metric z) =
      stateProfile D S C z.1) :
    scalarStateResidual D S (n08ScalarState metric z) = scalarResidualField D S C z := by
  have hprim : ∀ r, HasDerivAt (scalarStatePrimitive D S (n08ScalarState metric z))
      (stateProfile D S C z.1 r) r := by
    intro r
    rw [← hprofile]
    exact scalarStatePrimitive_hasDerivAt hN.1.1 hT hS _ r
  change normalizedHeightResidual (scalarStateProfile D S (n08ScalarState metric z))
      (Radial.radialHeightField (scalarStatePrimitive D S (n08ScalarState metric z)))
      (scalarStateIncrement S (n08ScalarState metric z)) z.2 =
    normalizedHeightResidual (stateProfile D S C z.1)
      (Radial.radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2
  rw [hprofile, n08ScalarState_increment]
  exact n08_normalizedHeightResidual_primitive_independent
    (scalarStatePrimitive_contDiff hN.1.1 hT hS _)
    (n08_stateRadialHeight_contDiff hT hS hN _)
    (contDiff_stateProfile_of_n01 hS hT hN _) hprim
    (n08_stateRadialHeight_hasDerivAt hT hS hN _)
    (n08_stateU_contDiff hT hS _) z.2

section Source

variable {v₀ : ScalarHeightSpace S} {W : WeightedScalarData S}

theorem n08_weightedResidual_compatible (hW : IsWeightedS04 D S v₀ W)
    {x : ScalarWeightedState S} (hx : x ∈ scalarStateBall S v₀ W.base W.epsilon) :
    S.Q (W.residual x) = 0 := by
  obtain ⟨_, _, J, _, hconservation, _⟩ := hW
  have h := (hconservation 0 x hx Fin.elim0).1
  rwa [J.zero x hx] at h

/-- This representative agrees with the actual S04 output on its open
domain and uses the source kernel as its codomain. -/
def n08WeightedResidualSource (hW : IsWeightedS04 D S v₀ W)
    (x : ScalarWeightedState S) : S.Source := by
  classical
  exact if hx : x ∈ scalarStateBall S v₀ W.base W.epsilon then
    ⟨W.residual x, n08_weightedResidual_compatible hW hx⟩ else 0

theorem n08WeightedResidualSource_coe (hW : IsWeightedS04 D S v₀ W)
    {x : ScalarWeightedState S} (hx : x ∈ scalarStateBall S v₀ W.base W.epsilon) :
    (n08WeightedResidualSource hW x).val = W.residual x := by
  unfold n08WeightedResidualSource
  rw [dif_pos hx]

theorem n08WeightedResidualSource_decode (hW : IsWeightedS04 D S v₀ W)
    {x : ScalarWeightedState S} (hx : x ∈ scalarStateBall S v₀ W.base W.epsilon)
    (p : PolarPoint) :
    (S.height scalarBeta).decode (n08WeightedResidualSource hW x).val p =
      scalarStateResidual D S x p := by
  rw [n08WeightedResidualSource_coe hW hx]
  exact hW.1 x hx p

theorem n08WeightedResidualSource_smoothTame (hW : IsWeightedS04 D S v₀ W) :
    SmoothTameOn (scalarStateGrading S) S.sourceGrading
      (scalarStateBall S v₀ W.base W.epsilon) (n08WeightedResidualSource hW) :=
  solve_smoothTameOn_codRestrict S.Q.toLinearMap.ker S.Q.isClosed_ker hW.2.1
    (n08WeightedResidualSource hW) (fun _ hx => n08WeightedResidualSource_coe hW hx)

end Source

end ContinuousFlexibility.Statements
