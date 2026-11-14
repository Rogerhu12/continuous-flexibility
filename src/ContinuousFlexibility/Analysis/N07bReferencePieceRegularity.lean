module

public import ContinuousFlexibility.Analysis.N07bCanonicalSourceJets
public import ContinuousFlexibility.Radial.ReferenceColumnSmooth

/-!
# Smooth representatives of the actual reference forcing on one piece

The current physical height is pulled back through the actual current inverse
and reference chart, with the actual height ratio. Boundary inverse germs give
infinite smoothness at every point of the reference physical closure. The
reference differential expression therefore has a smooth closed-piece
canonical representative even when a global reference field has only finite
regularity across interfaces.

All differential equalities are germ equalities of the actual slice
derivatives. Neither smoothness of the global forcing nor membership in a
canonical source space is an assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual radial expression written using the actual mixed slice jets.
This identity needs no differentiability hypothesis. -/
theorem n07b_radialPDE_eq_mixedJets (w : ℝ → ℝ)
    (u : PolarPoint → ℝ) (p : PolarPoint) :
    radialPDE w (fun r θ => u (r, θ)) p.1 p.2 =
      mixedDerivative 1 0
        (fun x => w x.1 * mixedDerivative 1 0 u x) p +
      deriv w p.1 / p.1 * mixedDerivative 0 2 u p := by
  simp only [radialPDE, mixedDerivative, iteratedDeriv_succ, iteratedDeriv_zero]

/-- The actual reference differential expression is smooth at each point
where its input is smooth. Profile flatness removes the quotient at radius
zero, without asking for one common neighborhood of infinite smoothness. -/
theorem n07b_contDiffAt_referencePDE {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u : PolarPoint → ℝ} {p : PolarPoint}
    (hu : ContDiffAt ℝ ∞ u p) :
    ContDiffAt ℝ ∞
      (fun x => radialPDE D.w (fun r θ => u (r, θ)) x.1 x.2) p := by
  have hflux : ContDiffAt ℝ ∞
      (fun x : PolarPoint => D.w x.1 * mixedDerivative 1 0 u x) p :=
    (hgeom.2.2.1.1.contDiffAt.comp p contDiffAt_fst).mul
      (contDiffAt_mixedDerivative hu 1 0)
  have hangular : ContDiffAt ℝ ∞
      (fun x : PolarPoint => deriv D.w x.1 / x.1) p :=
    (reference_contDiff_flat_deriv_div hgeom.1 hgeom.2.2.1).contDiffAt.comp p
      contDiffAt_fst
  have heq : (fun x => radialPDE D.w (fun r θ => u (r, θ)) x.1 x.2) =
      (fun x => mixedDerivative 1 0
        (fun y => D.w y.1 * mixedDerivative 1 0 u y) x +
        deriv D.w x.1 / x.1 * mixedDerivative 0 2 u x) :=
    funext (n07b_radialPDE_eq_mixedJets D.w u)
  rw [heq]
  exact (contDiffAt_mixedDerivative hflux 1 0).add
    (hangular.mul (contDiffAt_mixedDerivative hu 0 2))

/-- Agreement on an open set determines the actual reference expression,
including its totalized derivatives. No extra regularity is needed. -/
theorem n07b_radialPDE_eqOn_of_isOpen (w : ℝ → ℝ)
    {U : Set PolarPoint} (hU : IsOpen U) {u v : PolarPoint → ℝ}
    (huv : EqOn u v U) :
    EqOn (fun p => radialPDE w (fun r θ => u (r, θ)) p.1 p.2)
      (fun p => radialPDE w (fun r θ => v (r, θ)) p.1 p.2) U := by
  have hrad := mixedDerivative_eqOn_of_isOpen hU huv 1 0
  have hflux : EqOn
      (fun p => w p.1 * mixedDerivative 1 0 u p)
      (fun p => w p.1 * mixedDerivative 1 0 v p) U := by
    intro p hp
    change w p.1 * mixedDerivative 1 0 u p = w p.1 * mixedDerivative 1 0 v p
    rw [hrad hp]
  have hdiv := mixedDerivative_eqOn_of_isOpen hU hflux 1 0
  have hang := mixedDerivative_eqOn_of_isOpen hU huv 0 2
  intro p hp
  change radialPDE w (fun r θ => u (r, θ)) p.1 p.2 =
    radialPDE w (fun r θ => v (r, θ)) p.1 p.2
  rw [n07b_radialPDE_eq_mixedJets w u p,
    n07b_radialPDE_eq_mixedJets w v p, hdiv hp, hang hp]

/-- The genuine reference-piece remainder, with no choice of seam values. -/
def n07bReferencePieceRemainder {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (u : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  K.height (C.referenceState, 0) m p *
    canonicalHeight S K z m u (K.chart (C.referenceState, 0) m p)

/-- The stored expression is exactly the actual height-ratio pullback. -/
theorem n07bReferencePieceRemainder_eq {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (u : PolarPoint → ℝ) (p : PolarPoint) :
    n07bReferencePieceRemainder C K z m u p =
      (K.height (C.referenceState, 0) m p /
        K.height z m (K.inverseChart z m (K.chart (C.referenceState, 0) m p))) *
          u (K.inverseChart z m (K.chart (C.referenceState, 0) m p)) := by
  simp only [n07bReferencePieceRemainder, canonicalHeight]
  ring

/-- The smooth canonical extension supplied by one actual reference piece. -/
def n07bReferencePieceCanonicalSource (D : ReferenceData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (u : PolarPoint → ℝ) : PolarPoint → ℝ :=
  canonicalSource S K (C.referenceState, 0) m
    (fun p => radialPDE D.w
      (fun r θ => n07bReferencePieceRemainder C K z m u (r, θ)) p.1 p.2)

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  (hK : N04PartA D S C K base ε)
  (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
  (hsref : stateSector S C.referenceState)
  (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)

include hK href hsref hz hs

/-- Closed-piece smoothness follows from the actual boundary chart,
positive height and genuine inverse germ. -/
theorem n07bReferencePieceRemainder_contDiffAt_closed
    (m : ℕ) {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m) :
    ContDiffAt ℝ ∞ (n07bReferencePieceRemainder C K z m u) p := by
  have hclosed := hK.boundary (C.referenceState, 0) href hsref m
  have hcanonical := hclosed.1 hp
  have hfields := hclosed.2.2.2.2.1 p hp
  have hheight := n04b_canonicalHeight_contDiffAt_closed hK hz hs m hcanonical hu
  change ContDiffAt ℝ ∞ (fun y => K.height (C.referenceState, 0) m y *
    canonicalHeight S K z m u (K.chart (C.referenceState, 0) m y)) p
  exact hfields.2.1.mul (hheight.comp p hfields.1)

/-- The actual reference PDE is smooth on the closed physical piece. -/
theorem n07bReferencePiecePDE_contDiffAt_closed
    (hgeom : RadialProfileGeometry D) (m : ℕ)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m) :
    ContDiffAt ℝ ∞
      (fun x => radialPDE D.w
        (fun r θ => n07bReferencePieceRemainder C K z m u (r, θ)) x.1 x.2) p :=
  n07b_contDiffAt_referencePDE hgeom
    (n07bReferencePieceRemainder_contDiffAt_closed hK href hsref hz hs m hu hp)

/-- These are actual smooth closed-canonical representatives, including the
endpoint values of the stored inverse. -/
theorem n07bReferencePieceCanonicalSource_contDiffAt_closed
    (hgeom : RadialProfileGeometry D) (m : ℕ)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {p : PolarPoint} (hp : p ∈ canonicalClosed S K m) :
    ContDiffAt ℝ ∞ (n07bReferencePieceCanonicalSource D C K z m u) p := by
  exact n07b_contDiffAt_canonicalSource_closed hK href hsref m
    (fun x hx =>
      n07bReferencePiecePDE_contDiffAt_closed hK href hsref hz hs hgeom m hu hx) hp

omit hz hs

/-- Any global representative agreeing on the reference piece has the
same actual canonical source there. Its global forcing may have only
finite regularity across the physical interfaces. -/
theorem n07bReferencePieceCanonicalSource_eqOn
    (m : ℕ) (u R : PolarPoint → ℝ)
    (hR : EqOn R (n07bReferencePieceRemainder C K z m u)
      (referencePhysicalPieceOpen S K m)) :
    EqOn (canonicalSource S K (C.referenceState, 0) m
      (fun p => radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2))
      (n07bReferencePieceCanonicalSource D C K z m u) (canonicalOpen S K m) := by
  have hpiece : EqOn R (n07bReferencePieceRemainder C K z m u)
      (physicalPieceOpen S K (C.referenceState, 0) m) := by
    rw [hK.referenceDomain m]
    exact hR
  have hpde := n07b_radialPDE_eqOn_of_isOpen D.w
    (hK.domains (C.referenceState, 0) href hsref m).1 hpiece
  intro p hp
  have hx := (hK.charts (C.referenceState, 0) href hsref m).2.1 hp
  change K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) *
      radialPDE D.w (fun r θ => R (r, θ))
        (K.inverseChart (C.referenceState, 0) m p).1
        (K.inverseChart (C.referenceState, 0) m p).2 /
      |planeJacobian (K.chart (C.referenceState, 0) m)
        (K.inverseChart (C.referenceState, 0) m p)| = _
  exact congrArg (fun value : ℝ =>
    K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) *
      value / |planeJacobian (K.chart (C.referenceState, 0) m)
        (K.inverseChart (C.referenceState, 0) m p)|) (hpde hx)

end ContinuousFlexibility.Analysis
