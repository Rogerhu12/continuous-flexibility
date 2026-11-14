module

public import ContinuousFlexibility.Analysis.ReturnCorrectionVelocityRegularity
public import ContinuousFlexibility.Analysis.N01FlowJointSmoothness

/-!
# Transport equations for the actual optical correction

The two inverse compositions used by the correction satisfy simple
radial equations.  The inverse angular slope is transported by the
original flow, while every independent displacement is transported by
the same corrected flow.  These identities retain the independent
circle argument and avoid repeated differentiation of two inverse maps.

All derivatives are actual Fréchet partial derivatives.  Their
existence follows from N01 and the already constructed inverse
regularity, rather than from a formal rule for inverse coordinates.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

local instance returnCorrectionTransportEquationsRealNormedSpace : NormedSpace ℝ ℝ :=
  NormedField.toNormedSpace

/-- The first angular variation, expressed in the current coordinate. -/
def returnFlowInverseSlope (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : ℝ :=
  deriv (C.minusFlow z m p.1) (Function.invFun (C.minusFlow z m p.1) p.2)

/-- The existing independent displacement in the actual corrected
inverse coordinate.  The state and both inverse maps remain frozen. -/
def returnCorrectionPulledDisplacementLinear (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : CircleSpace S →ₗ[ℝ] ℝ :=
  returnCorrectionDisplacementLinear S C z m
    (Function.invFun (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m))
      (Function.invFun (C.minusFlow z m p.1) p.2))

theorem returnCorrectionVelocityLinear_eq_transportProduct
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (ρ : CircleSpace S) :
    returnCorrectionVelocityLinear D S C χ z m p ρ =
      deriv (χ m) p.1 * returnFlowInverseSlope S C z m p *
        returnCorrectionPulledDisplacementLinear S C χ z m p ρ := by
  rw [returnCorrectionVelocityLinear_apply]
  dsimp only [returnFlowInverseSlope, returnCorrectionPulledDisplacementLinear]
  ring

theorem returnFlowInverseSlope_on_flow
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ)
    (hF : Function.Injective (C.minusFlow z m r)) :
    returnFlowInverseSlope S C z m (r, C.minusFlow z m r θ) =
      deriv (C.minusFlow z m r) θ := by
  unfold returnFlowInverseSlope
  exact congrArg (deriv (C.minusFlow z m r)) (Function.leftInverse_invFun hF θ)

theorem returnCorrectionPulledDisplacementLinear_on_flow
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ)
    (hF : Function.Injective (C.minusFlow z m r))
    (hJ : Function.Injective (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m)))
    (ρ : CircleSpace S) :
    returnCorrectionPulledDisplacementLinear S C χ z m
        (r, returnCorrectedMinusFlow S C χ z m r θ) ρ =
      returnCorrectionDisplacementLinear S C z m θ ρ := by
  unfold returnCorrectionPulledDisplacementLinear returnCorrectedMinusFlow
  exact congrArg (fun α : ℝ => returnCorrectionDisplacementLinear S C z m α ρ)
    ((congrArg
      (Function.invFun (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m)))
      (Function.leftInverse_invFun hF
        (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ))).trans
      (Function.leftInverse_invFun hJ θ))

/-- A differentiable field evaluated along a genuine characteristic
curve has the corresponding transport derivative. -/
theorem scalar_transport_identity_of_curve
    {u : PolarPoint → ℝ} {γ : ℝ → ℝ} {r c d : ℝ}
    (hu : DifferentiableAt ℝ u (r, γ r)) (hγ : HasDerivAt γ c r)
    (hcomp : HasDerivAt (fun s => u (s, γ s)) d r) :
    radialPartial u (r, γ r) + c * angularPartial u (r, γ r) = d := by
  let A : PolarPoint →L[ℝ] ℝ := fderiv ℝ u (r, γ r)
  have hd : HasDerivAt (fun s => u (s, γ s)) (A (1, c)) r := by
    simpa only [Function.comp_def, id_eq, A] using
      hu.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).prodMk hγ)
  have hcoord : A (1, c) = radialPartial u (r, γ r) +
      c * angularPartial u (r, γ r) := by
    have h := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, c))
      (returnFlow_linearMap_coordinates A)
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
      mul_one, one_mul, A, radialPartial, angularPartial, mul_comm] using h
  exact hcoord.symm.trans (hd.unique hcomp)

theorem N01Properties.minusFlow_slice_bijective
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    Function.Bijective (C.minusFlow z m r) := by
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  refine ⟨(strictMono_of_deriv_pos (fun θ => ((hflow z hz m θ).2.2.2 r hr).1)).injective, ?_⟩
  exact returnLift_surjective Real.pi_pos
    (N01Properties.minusFlow_differentiable S C z m hN hz hr).continuous
    (hN.minusFlow_add_period hz m hr)

section ActualTransport

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN hS hT hz hsector

theorem N01Properties.returnInterpolation_slice_bijective
    (m : ℕ) (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) :
    Function.Bijective (returnInterpolation c (returnCorrectionInitialMap S C z m)) := by
  have hK := hN.returnCorrectionInitialMap_contDiff hS hT hz hsector m
  refine ⟨(returnInterpolation_strictMono hc.1 hc.2
    (hN.returnCorrectionInitialMap_strictMono hz hsector m)).injective, ?_⟩
  have hcont : Continuous (returnInterpolation c (returnCorrectionInitialMap S C z m)) :=
    continuous_id.add (continuous_const.mul (hK.continuous.sub continuous_id))
  exact returnLift_surjective Real.pi_pos hcont
    (returnInterpolation_periodic_lift
      (hN.returnCorrectionInitialMap_add_period hz hsector m) c)

theorem N01Properties.returnFlowInverseSlope_contDiffAt_one
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ 1 (returnFlowInverseSlope S C z m) p := by
  have hi := hN.minusFlow_invFun_contDiffAt_one hS hT hz hsector m p hp
  have hJ := hN.minusFlow_angular_deriv_contDiffAt_one hS hT hz hsector m
    (p.1, Function.invFun (C.minusFlow z m p.1) p.2) hp
  exact hJ.comp p (contDiffAt_fst.prodMk hi)

theorem N01Properties.returnCorrectionPulledDisplacementLinear_contDiffAt_one
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (hχ : ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ 1
      (fun q => returnCorrectionPulledDisplacementLinear S C χ z m q ρ) p := by
  let A : PolarPoint → ℝ := fun q => Function.invFun (C.minusFlow z m q.1) q.2
  let B : PolarPoint → ℝ := fun q => Function.invFun
    (returnInterpolation (χ m q.1) (returnCorrectionInitialMap S C z m)) (A q)
  have hA : ContDiffAt ℝ 1 A p :=
    hN.minusFlow_invFun_contDiffAt_one hS hT hz hsector m p hp
  have hJ : ContDiffAt ℝ 1 (fun q : PolarPoint => Function.invFun
      (returnInterpolation (χ m q.1) (returnCorrectionInitialMap S C z m)) q.2) (p.1, A p) :=
    (hN.returnInterpolation_invFun_contDiffAt hS hT hz hsector χ m hχ hχrange
      (p.1, A p) hp).of_le (by simp)
  have hpull : ContDiffAt ℝ 1 (fun q : PolarPoint => (q.1, A q)) p :=
    contDiffAt_fst.prodMk hA
  have hB : ContDiffAt ℝ 1 B p :=
    (hJ.comp p hpull).congr_of_eventuallyEq (Eventually.of_forall fun q => rfl)
  exact ((hN.returnCorrectionDisplacementLinear_contDiff hS hT hz hsector m ρ).contDiffAt.of_le
    (by simp)).comp p hB

theorem N01Properties.returnFlowInverseSlope_transport
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    radialPartial (returnFlowInverseSlope S C z m) p =
      characteristicAngularDerivative D S C z p * returnFlowInverseSlope S C z m p -
        minusCharacteristicSpeed (originalCoefficients D S C z) p *
          angularPartial (returnFlowInverseSlope S C z m) p := by
  rcases p with ⟨r, θ⟩
  have hclosed : r ∈ Icc (C.left m) (C.right m) := ⟨hp.1.le, hp.2.le⟩
  obtain ⟨α, rfl⟩ := (hN.minusFlow_slice_bijective hz m hclosed).2 θ
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hcurve := (hflow z hz m α).2.2.1 r hp
  have hreg := (hN.returnFlowInverseSlope_contDiffAt_one hS hT hz hsector m
    (r, C.minusFlow z m r α) hp).differentiableAt (by simp)
  have hcomp : HasDerivAt
      (fun s => returnFlowInverseSlope S C z m (s, C.minusFlow z m s α))
      (characteristicAngularDerivative D S C z (r, C.minusFlow z m r α) *
        deriv (C.minusFlow z m r) α) r := by
    apply (hN.minusFlow_angular_deriv_hasDerivAt_radial hS hT hz hsector m hp α).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with s hs
    exact returnFlowInverseSlope_on_flow S C z m s α
      (hN.minusFlow_slice_bijective hz m ⟨hs.1.le, hs.2.le⟩).1
  have hid := scalar_transport_identity_of_curve hreg hcurve hcomp
  have hvalue := returnFlowInverseSlope_on_flow S C z m r α
    (hN.minusFlow_slice_bijective hz m hclosed).1
  rw [← hvalue] at hid
  linarith only [hid]

theorem N01Properties.returnFlowInverseSlope_transport_of_discriminant
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    radialPartial (returnFlowInverseSlope S C z m) p =
      angularPartial (minusCharacteristicSpeed (originalCoefficients D S C z)) p *
          returnFlowInverseSlope S C z m p -
        minusCharacteristicSpeed (originalCoefficients D S C z) p *
          angularPartial (returnFlowInverseSlope S C z m) p := by
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hp.1, hp.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hfull := (hN.minusCharacteristicSpeed_contDiffAt_of_discriminant
    hS hT hz hsector hpD hdisc).differentiableAt (by simp)
  have heq := (hN.minusCharacteristicSpeed_hasDerivAt_angular
    hS hT hz hsector hpD.1 p.2).unique (hasDerivAt_angular_slice hfull)
  exact (hN.returnFlowInverseSlope_transport hS hT hz hsector m p hp).trans
    (congrArg (fun d : ℝ => d * returnFlowInverseSlope S C z m p -
      minusCharacteristicSpeed (originalCoefficients D S C z) p *
        angularPartial (returnFlowInverseSlope S C z m) p) heq)

theorem N01Properties.returnCorrectionPulledDisplacementLinear_transport
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (hχ : ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    radialPartial (fun q => returnCorrectionPulledDisplacementLinear S C χ z m q ρ) p =
      -returnCorrectedMinusSpeed D S C χ z m p *
        angularPartial (fun q => returnCorrectionPulledDisplacementLinear S C χ z m q ρ) p := by
  rcases p with ⟨r, θ⟩
  have hclosed : r ∈ Icc (C.left m) (C.right m) := ⟨hp.1.le, hp.2.le⟩
  have hsurj : Function.Surjective (returnCorrectedMinusFlow S C χ z m r) :=
    (hN.minusFlow_slice_bijective hz m hclosed).2.comp
      (hN.returnInterpolation_slice_bijective hS hT hz hsector m (χ m r) (hχrange r hclosed)).2
  obtain ⟨α, rfl⟩ := hsurj θ
  have hreg := (hN.returnCorrectionPulledDisplacementLinear_contDiffAt_one
    hS hT hz hsector χ m hχ hχrange ρ
      (r, returnCorrectedMinusFlow S C χ z m r α) hp).differentiableAt (by simp)
  have hF := (hN.minusFlow_hasStrictFDerivAt hS hT hz hsector m
    (r, returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) α) hp).hasFDerivAt.differentiableAt
  have hcurve := hN.returnCorrectedMinusFlow_hasDerivAt χ hz hsector m r α hp
    (hχ.differentiable (by simp) r) (hχrange r hclosed) hF
  have hcomp : HasDerivAt (fun s => returnCorrectionPulledDisplacementLinear S C χ z m
      (s, returnCorrectedMinusFlow S C χ z m s α) ρ) 0 r := by
    apply (hasDerivAt_const r (returnCorrectionDisplacementLinear S C z m α ρ)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with s hs
    have hsclosed : s ∈ Icc (C.left m) (C.right m) := ⟨hs.1.le, hs.2.le⟩
    exact returnCorrectionPulledDisplacementLinear_on_flow S C χ z m s α
      (hN.minusFlow_slice_bijective hz m hsclosed).1
      (hN.returnInterpolation_slice_bijective hS hT hz hsector m (χ m s)
        (hχrange s hsclosed)).1 ρ
  have hid := scalar_transport_identity_of_curve hreg hcurve hcomp
  linarith only [hid]

theorem N01Properties.returnCorrectionPulledDisplacementLinear_transport_actual
    {R : ReturnEquationData S} (hR : N02Properties D T S C R base ε)
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (hχ : ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    radialPartial (fun q => returnCorrectionPulledDisplacementLinear S C χ z m q ρ) p =
      -(minusCharacteristicSpeed (originalCoefficients D S C z) p +
          deriv (χ m) p.1 * returnFlowInverseSlope S C z m p *
            returnCorrectionPulledDisplacementLinear S C χ z m p (R.residual z)) *
        angularPartial (fun q => returnCorrectionPulledDisplacementLinear S C χ z m q ρ) p := by
  have hvelocity := returnCorrectionVelocityLinear_at_actual hN hR χ hz hsector m p
  rw [returnCorrectionVelocityLinear_eq_transportProduct] at hvelocity
  have hspeed : returnCorrectedMinusSpeed D S C χ z m p =
      minusCharacteristicSpeed (originalCoefficients D S C z) p +
        deriv (χ m) p.1 * returnFlowInverseSlope S C z m p *
          returnCorrectionPulledDisplacementLinear S C χ z m p (R.residual z) := by
    linarith only [hvelocity]
  exact (hN.returnCorrectionPulledDisplacementLinear_transport
    hS hT hz hsector χ m hχ hχrange ρ p hp).trans
      (congrArg (fun c : ℝ => -c * angularPartial
        (fun q => returnCorrectionPulledDisplacementLinear S C χ z m q ρ) p) hspeed)

end ActualTransport

end ContinuousFlexibility.Statements
