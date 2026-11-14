module

public import ContinuousFlexibility.Analysis.N07bReferenceBulkEnergy
public import ContinuousFlexibility.Analysis.N07bReferenceForcingSymmetry
public import ContinuousFlexibility.Analysis.N07bCanonicalSourceSymmetry
public import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# The canonical bulk source of the actual global reference remainder

A positive height exponent gives global smoothness of the original physical
height. The actual reference remainder need only agree with the genuine local
pullbacks on each reference piece and have the required angular symmetries.
Its PDE has those same symmetries, while local closed-piece representatives
supply the canonical jet regularity. The energy bound therefore produces an
element of the prescribed volume level for this actual global forcing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The actual global remainder supplies every local regularity and
symmetry input of the reference bulk lift. No regularity or norm bound on
its global PDE forcing is assumed. -/
theorem n07b_exists_referenceBulkLift_of_remainder
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (hK : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {β : ℝ} (hβ : 0 < β) {u R : PolarPoint → ℝ}
    (hu : HeightMember D T β u)
    (hR : ∀ m, EqOn R (n07bReferencePieceRemainder C K z m u)
      (referencePhysicalPieceOpen S K m))
    (hRp : Function.Periodic R (0, Real.pi))
    (hRe : ∀ r θ, R (r, -θ) = R (r, θ)) (b : ℕ)
    {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m x, x ∈ physicalPieceOpen S K z m →
      ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
        (n07bSourceNormalizer T K z m β x *
          n07bReferenceBulkCoefficient D T C K z m β j.val i x) ^ 2 ≤ A * T.M x.1 ^ 2) :
    ∃ F : V.level β 0 b,
      (∀ m, (V.forget β 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m
          (fun p => radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2)) ∧
      ‖F‖ ^ 2 ≤ A * n07bReferenceBulkPathConstant b * physicalNorm T β (b + 3) u ^ 2 := by
  have husmooth : ContDiff ℝ ∞ u := (heightMember_contDiff_and_flatJets hT hβ hu).1
  let P : PolarPoint → ℝ := fun p => radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2
  let g : ℕ → PolarPoint → ℝ := fun m => canonicalSource S K (C.referenceState, 0) m P
  have hge (m : ℕ) : EqOn (g m) (n07bReferencePieceCanonicalSource D C K z m u)
      (canonicalOpen S K m) :=
    n07bReferencePieceCanonicalSource_eqOn hK href hsref m u R (hR m)
  have he (m : ℕ) (p : PolarPoint) (hp : p ∈ canonicalClosed S K m) :
      ContDiffAt ℝ ∞ (n07bReferencePieceCanonicalSource D C K z m u) p :=
    n07bReferencePieceCanonicalSource_contDiffAt_closed hK href hsref hz hs
      hD.choose_spec.1 m husmooth hp
  have hPperiod : Function.Periodic P (0, Real.pi) := n07b_radialPDE_periodic D.w hRp
  have hPeven : ∀ r θ, P (r, -θ) = P (r, θ) := n07b_radialPDE_even D.w hRe
  have hp (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (K.left m) (K.right m)) :
      Function.Periodic (fun θ => g m (r, θ)) Real.pi :=
    n07b_canonicalSource_periodic hK href hsref P hPperiod m hr
  have hr (m : ℕ) : (fun p : PolarPoint => g m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] g m :=
    n07b_canonicalSource_reflection_ae hK href hsref P hPeven hPperiod m
  exact n07b_exists_referenceBulkLift hK href hsref hz hs hD hT hV β hu b g
    hge he hp hr hA hcoeff

end ContinuousFlexibility.Analysis
