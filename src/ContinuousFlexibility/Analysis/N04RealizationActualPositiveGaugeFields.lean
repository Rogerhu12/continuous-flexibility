module

public import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
public import ContinuousFlexibility.Analysis.PositiveReferenceCylinder
public import ContinuousFlexibility.Analysis.N04RealizationPotentialIdentity

/-!
# The actual positive fields at the same inverse point

The displayed whole atlas retains the supplied reference functions Y/H.
Its positive height and inverse fields therefore give the fixed radial
pullback formula at their own actual inverse point. The constant-test
operator identity then identifies the stored positive potential using
these same fields and the stored principal coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

variable {D : ReferenceData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

/-- The exact same-atlas fields use the original relative inverse and
the prescribed reference inverse. No moving point is replaced. -/
theorem n04Realization_actualPositive_pulledHeight
    (z : AnnularState S × ℝ) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hστ : Function.LeftInverse (σ z i) (τ z i)) (q : PolarPoint) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell
      (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j))
      (fun j p => H j p.1) τ σ Q N
    V.height z m (V.inverseChart z m q) =
        H i (Function.invFun (Y i) q.1) *
          (Q z i (Function.invFun (Y i) q.1, q.2))⁻¹ ∧
      (V.height z m (V.inverseChart z m q))⁻¹ =
        (H i (Function.invFun (Y i) q.1))⁻¹ *
          Q z i (Function.invFun (Y i) q.1, q.2) := by
  let V := n04WholeReferenceGaugeAtlasData C L K e cell
    (fun j => positiveReferenceCylinderChart (Y j))
    (fun j => positiveReferenceCylinderInverse (Y j))
    (fun j p => H j p.1) τ σ Q N
  have hv := n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell
    (fun j => positiveReferenceCylinderChart (Y j))
    (fun j => positiveReferenceCylinderInverse (Y j))
    (fun j p => H j p.1) τ σ Q N z m i hi
  have hvG : V.inverseChart z m =
      wholePositiveReferenceGaugeInverse (τ z i) (positiveReferenceCylinderInverse (Y i)) :=
    hv.2.2.2.2.2.2.2.2.1
  have hvH : V.height z m = wholePositiveReferenceGaugeHeight (fun p => H i p.1)
      (σ z i) (Q z i) := hv.2.2.2.2.2.2.2.2.2.1
  have heq : V.height z m (V.inverseChart z m q) =
      H i (Function.invFun (Y i) q.1) /
        Q z i (Function.invFun (Y i) q.1, q.2) := by
    rw [hvH, hvG, wholePositiveReferenceGaugeHeight_eq,
      wholePositiveReferenceGaugeInverse, Function.comp_apply,
      hστ (positiveReferenceCylinderInverse (Y i) q)]
    simp only [positiveReferenceCylinderInverse]
  change V.height z m (V.inverseChart z m q) = _ ∧
    (V.height z m (V.inverseChart z m q))⁻¹ = _
  rw [heq]
  exact ⟨div_eq_mul_inv _ _, by rw [inv_div, div_eq_mul_inv, mul_comm]⟩

/-- On the actual positive canonical piece the stored potential is the
positive-sign reciprocal-height divergence of its stored principal
field, in the supplied fixed reference gauge. -/
theorem n04Realization_actualPositive_potential
    {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C
      (n04WholeReferenceGaugeAtlasData C L K e cell
        (fun j => positiveReferenceCylinderChart (Y j))
        (fun j => positiveReferenceCylinderInverse (Y j))
        (fun j p => H j p.1) τ σ Q N) base ε)
    (hB : N04PartB S C L
      (n04WholeReferenceGaugeAtlasData C L K e cell
        (fun j => positiveReferenceCylinderChart (Y j))
        (fun j => positiveReferenceCylinderInverse (Y j))
        (fun j p => H j p.1) τ σ Q N) base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hστ : Function.LeftInverse (σ z i) (τ z i))
    {q : PolarPoint} (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell
      (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j))
      (fun j p => H j p.1) τ σ Q N
    V.potential z m q =
      (H i (Function.invFun (Y i) q.1) *
        (Q z i (Function.invFun (Y i) q.1, q.2))⁻¹) *
      divergenceOperator (V.coefficients z m)
        (fun p => (H i (Function.invFun (Y i) p.1))⁻¹ *
          Q z i (Function.invFun (Y i) p.1, p.2)) q := by
  let V := n04WholeReferenceGaugeAtlasData C L K e cell
    (fun j => positiveReferenceCylinderChart (Y j))
    (fun j => positiveReferenceCylinderInverse (Y j))
    (fun j p => H j p.1) τ σ Q N
  have hv := n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell
    (fun j => positiveReferenceCylinderChart (Y j))
    (fun j => positiveReferenceCylinderInverse (Y j))
    (fun j p => H j p.1) τ σ Q N z m i hi
  have hleft : V.left m = 0 := hv.1
  have hright : V.right m = 1 := hv.2.1
  have hpositive : V.positive m = true := hv.2.2.2.2.2.2.1
  have hqV : q ∈ canonicalOpen S V m := by
    simpa only [canonicalOpen, hleft, hright] using hq
  have hpull (p : PolarPoint) :=
    n04Realization_actualPositive_pulledHeight C L K e cell Y H τ σ Q N z m i hi hστ p
  have hinv : (fun p => (V.height z m (V.inverseChart z m p))⁻¹) =
      (fun p => (H i (Function.invFun (Y i) p.1))⁻¹ *
        Q z i (Function.invFun (Y i) p.1, p.2)) := by
    funext p
    exact (hpull p).2
  have hp := n04Realization_canonicalPotential_eq_reciprocalHeight_divergence
    hA hB hz hs m hqV
  rw [hpositive, if_pos rfl, neg_neg, one_mul, (hpull q).1, hinv] at hp
  exact hp

end ContinuousFlexibility.Analysis
