module

public import ContinuousFlexibility.Analysis.CanonicalWholePositiveRootMatching
public import ContinuousFlexibility.Analysis.CanonicalWholeNegativeBoundary
public import ContinuousFlexibility.Analysis.WholeComponentFieldGluing
public import ContinuousFlexibility.Analysis.WholeComponentFieldSymmetries

/-!
# Ordinary finite regularity of the actual global relative fields

The existing radius selector glues the retained negative transport to
the constructed whole-positive transport. Its actual endpoint matching
gives one more derivative for the coordinate than for the height. The
same selected fields preserve the open annulus and the positive height.
No global regularity or matching conclusion is supplied as an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- For the fixed construction order `n = 3`, both stored global fields
are C3. Increasing a requested estimate order never changes these fields. -/
theorem n04WholeCanonical_global_relative_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (n : ℕ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (τ σ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (c d J H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hm : ∀ i,
      let K := n04bActualTypedAtlas hT hS hN hfield e
      WholePositiveTransportMatching n
        (fun side => n04PositiveSourceMap (j i side) K z)
        (fun side => n04PositiveSourceHeight (j i side) K z)
        (τ i) (σ i) (Q i) (n04PositiveLeft i) (n04PositiveRight i)
        (c i) (d i) (J i) (H i)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let F := n04WholeComponentField C (canonicalWholeNegativeTransport C K z) τ id
    let q := n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) Q
      (fun _ => (1 : ℝ))
    ContDiffOn ℝ (n + 1) F (annularOpen D) ∧
      ContDiffOn ℝ n q (annularOpen D) ∧
      MapsTo F (annularOpen D) (annularOpen D) ∧
      ∀ p ∈ annularOpen D, 0 < q p := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hmatch (i : N04PositiveComponent D.a D.b (deriv D.w)) :
      WholePositiveNegativeRootJets n C K z i (τ i) (Q i) :=
    wholePositiveTransportMatching_negative_root_jets hN.1.1 (j i) (hm i)
  have hclosed (m : ℕ) (p : PolarPoint)
      (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
      ContDiffAt ℝ ∞ (canonicalWholeNegativeTransport C K z m) p ∧
        ContDiffAt ℝ ∞ (canonicalWholeNegativeHeightRatio C K z m) p ∧
        0 < canonicalWholeNegativeHeightRatio C K z m p :=
    canonicalWholeNegativeTransport_closed_regular hT hS hN hfield e hz hs m
      ⟨hp, mem_univ _⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply n04WholeComponentField_contDiffOn (n + 1) hN.1.1
      (canonicalWholeNegativeTransport C K z) τ id
    · intro m p hp
      exact (hclosed m p hp).1.of_le (by simp)
    · intro i
      exact (hm i).geometry.smooth.of_le (by simp)
    · intro m side i hadj θ k hk
      exact (hmatch i m side hadj).1 θ k hk
  · apply n04WholeComponentField_contDiffOn n hN.1.1
      (canonicalWholeNegativeHeightRatio C K z) Q (fun _ => (1 : ℝ))
    · intro m p hp
      exact (hclosed m p hp).2.1.of_le (by simp)
    · intro i
      exact (hm i).height_smooth.of_le (by simp)
    · intro m side i hadj θ k hk
      exact (hmatch i m side hadj).2 θ k hk
  · exact n04WholeComponentField_mapsTo_annulus hN.1.1
      (canonicalWholeNegativeTransport C K z) τ id
      (fun m => canonicalWholeNegativeTransport_mapsTo_closed hT hS hN hfield e hz hs m)
      (fun i => (hm i).geometry.maps_open)
  · intro p hp
    have hD : RadialProfileGeometry D := (Classical.choose_spec hN.1.1.1.1).1
    have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
    have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
    rcases n04_wholeComponent_cover hD hC hp.1 with ⟨m, hm⟩ | ⟨i, hi⟩
    · rw [n04WholeComponentField_eq_negative hN.1.1
        (canonicalWholeNegativeHeightRatio C K z) Q (fun _ => (1 : ℝ)) hm]
      exact (hclosed m p hm).2.2
    · rw [n04WholeComponentField_eq_positive hf hC
        (canonicalWholeNegativeHeightRatio C K z) Q (fun _ => (1 : ℝ)) hi]
      exact (hm i).height_positive p

end ContinuousFlexibility.Analysis
