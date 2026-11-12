import ContinuousFlexibility.Analysis.N06FiniteCurrentBoundaryGluing
import ContinuousFlexibility.Analysis.N06PositiveBoundaryPrincipal
import ContinuousFlexibility.Analysis.N06PositiveDividedRegularity

/-!
# The actual signed radial factor and the finite Green endpoint row

The original forward chart fixes the sign of its radial first jet at
both endpoints. That sign is exactly the reversal flag used by the
finite-atlas Green formula. At a boundary with nonnegative reference
slope, the transported normal row is the positive reference radial
coefficient or the negative normal-form coefficient one. These are
derived boundary densities, not assigned values of a totalized inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- The actual radial Jacobian sign is the chart reversal sign. It is
deduced from the map and its true nonzero derivative at the endpoint. -/
theorem n06_current_boundary_radialSign_eq_reverse
    (reverse physicalUpper : Bool)
    {σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets (K.chart z m) (K.height z m)
      (n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper)
      (n06Endpoint (K.left m) (K.right m)
        (if reverse then !physicalUpper else physicalUpper)) σ β H ρ κ Hr)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hx : ∀ η, (n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper, η) ∈
      physicalPieceClosed S K z m)
    (hside : ∀ p ∈ physicalPieceOpen S K z m,
      if physicalUpper then p.1 < K.physicalRight m else K.physicalLeft m < p.1)
    (θ : ℝ) :
    (σ * ρ θ) / |σ * ρ θ| = if reverse then (-1 : ℝ) else 1 := by
  have he := (n06_current_boundary_radial_orientation physicalUpper
    (if reverse then !physicalUpper else physicalUpper) J h04 hz hs hx hside θ).2
  cases reverse <;> cases physicalUpper <;>
    simp only [n06EndpointSign, Bool.false_eq_true, if_false, if_true,
      Bool.not_false, Bool.not_true, one_mul, neg_one_mul] at he ⊢ <;>
    linarith only [he]

/-- The normal row used by the actual finite Green formula follows
from the actual positive coefficient germs and the negative normal form.
No endpoint coefficient or inverse value is imposed as a hypothesis. -/
theorem n06_nonnegative_boundaryDensity
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (a : ℕ → ℝ → ℝ)
    (ha : ∀ n, K.positive n = true → Continuous (a n))
    (hea : ∀ n, K.positive n = true → EqOn (K.coefficients (C.referenceState, 0) n).a
      (fun p => a n p.1) (canonicalOpen S K n))
    (heb : ∀ n, K.positive n = true → EqOn (K.coefficients (C.referenceState, 0) n).b
      (fun _ => 0) (canonicalOpen S K n))
    (hreg : ∀ n, K.positive n = true →
      ContDiffOn ℝ ∞ (K.coefficients z n).a (canonicalOpen S K n) ∧
      ContDiffOn ℝ ∞ (K.coefficients z n).b (canonicalOpen S K n) ∧
      ContDiffOn ℝ ∞ (K.coefficients z n).c (canonicalOpen S K n))
    (canonicalUpper : Bool) {r σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets (K.chart z m) (K.height z m) r
      (n06Endpoint (K.left m) (K.right m) canonicalUpper) σ β H ρ κ Hr)
    (hx : ∀ η, (r, η) ∈ physicalPieceClosed S K z m)
    (hp : r ∈ radialCore D) (hpos : 0 ≤ deriv D.w r)
    (θ : ℝ) (Q Qr Qt W : PolarPoint → ℝ) :
    n06RootBoundaryDensity (L.coefficients z) (K.chart z m) (K.height z m)
      Q Qr Qt W (r, θ) (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ) =
      (if K.positive m = true then a m (n06Endpoint (K.left m) (K.right m) canonicalUpper)
        else 1) *
        (Q (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ) *
          radialPartial W (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ) -
        W (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ) *
          Qr (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ)) := by
  by_cases hm : K.positive m = true
  · rw [if_pos hm]
    apply n06_positive_root_boundaryDensity hT hS h01 h03 h04 hz hs hm
      (ha m hm) (hea m hm) (heb m hm) ?_ canonicalUpper J hx hp θ Q Qr Qt W
    intro x hx
    have he := n06_positive_physical_density_of_regular_coefficients
      hT hS h01 h03 h04 hz hs m hm (hreg m hm) hx
    exact ⟨he.1, he.2.1⟩
  · have hrow := n06_negative_closed_normalDensity_of_nonneg hT hS h01 h03 h04 hz hs
      m (Bool.eq_false_of_not_eq_true hm) (x := (r, θ)) (hx θ) ⟨hp, mem_univ _⟩ hpos
    simp only [n06RootBoundaryDensity, hrow.1, hrow.2, if_neg hm,
      one_mul, zero_mul, add_zero]

end ContinuousFlexibility.Statements
