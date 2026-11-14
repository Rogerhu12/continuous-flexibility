module

public import ContinuousFlexibility.Analysis.N07aTubularPhysicalGluing
public import ContinuousFlexibility.Analysis.N07aPhysicalPieceEquation
public import ContinuousFlexibility.Analysis.N07aLocalPullbackNoncharacteristic
public import ContinuousFlexibility.Analysis.N07aCurrentFirstTraces
public import ContinuousFlexibility.Analysis.N07aReconstructionEquationData
public import ContinuousFlexibility.Analysis.N07aReferenceReturn

/-!
# The actual canonical unknown is smooth across every moving cut

First traces come from its original reference graph. The current
canonical equation gives the physical equation of each closed height.
The noncharacteristic coefficient comes from the actual N04 operator
identity. These proved inputs feed the common tubular-coordinate gluing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_actualCanonical_cut_smooth_gluing
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hborder : RadialTrueBorder D)
    (z : CanonicalGeometry.Parameter S)
    (hz : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    {U : CanonicalUnknown S K}
    (hreference : N07aReferenceGraphRepresentation D S C K U)
    {v : ℕ → PolarPoint → ℝ}
    (hv : ∀ m, ContDiffOn ℝ ∞ (v m) (canonicalOpen S K m))
    (hvp : ∀ m, Function.Periodic (v m) (0, Real.pi))
    (hvae : ∀ m, (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v m)
    (J : ∀ m, ClosedJetTower (K.left m) (K.right m) (v m))
    (f : S.Source) (heq : N07aActualNormalEquation D S C L K z U f v)
    (k : ℕ) (θ₀ : ℝ)
    (B : N07aTubularCutCoordinates S C K (liftSectorParameter S C z) k θ₀) :
    ∃ O : Set PolarPoint, IsOpen O ∧
      canonicalCutPoint S K (liftSectorParameter S C z) k θ₀ ∈ O ∧
      ∃ w : PolarPoint → ℝ, ContDiffOn ℝ ∞ w O ∧
        EqOn w (n07aClosedPhysicalHeight K (liftSectorParameter S C z)
          (K.cutPair k).1 (J (K.cutPair k).1))
          (O ∩ physicalPieceOpen S K (liftSectorParameter S C z) (K.cutPair k).1) ∧
        EqOn w (n07aClosedPhysicalHeight K (liftSectorParameter S C z)
          (K.cutPair k).2 (J (K.cutPair k).2))
          (O ∩ physicalPieceOpen S K (liftSectorParameter S C z) (K.cutPair k).2) := by
  classical
  let x := liftSectorParameter S C z
  let i := (K.cutPair k).1
  let j := (K.cutPair k).2
  obtain ⟨hi, hj, _, _, _, hR, hli, _, hri, _⟩ := h04.2.1.1.1 k
  obtain ⟨γ, M₀, M₁, Fref, ηref, fref, hrep, hgraph⟩ := hreference
  have htrace (θ : ℝ) := n07a_currentRepresentation_cut_firstJets hD hS hborder
    h04 hcanonical (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector
    hz hs hrep hgraph hvae hvp J k θ
  have hcoeff := hcanonical.physicalCoefficients x hz hs
  have hcore : Ioo (C.left k) (C.right k) ⊆ Ioo D.a D.b := by
    have hC := h01.2.2.2.1.1 k
    exact fun r hr => ⟨hC.1.trans hr.1, hr.2.trans hC.2.2⟩
  have hcenter : (K.cutRadius k, θ₀) ∈
      Icc B.left B.right ×ˢ Icc B.lower B.upper :=
    ⟨⟨B.left_lt.le, B.lt_right.le⟩, ⟨B.lower_lt.le, B.lt_upper.le⟩⟩
  have hcenterTarget : canonicalCutPoint S K x k θ₀ ∈ B.e.target := by
    rw [← B.cut_eq θ₀]
    exact B.e.map_source (B.closed_source hcenter)
  have hcenterD : canonicalCutPoint S K x k θ₀ ∈ annularOpen D := by
    have hp := B.component hcenter
    rw [B.cut_eq θ₀] at hp
    exact ⟨hcore hp.1, mem_univ _⟩
  have hcanon : (K.cutRadius k, θ₀) ∈ canonicalClosed S K i := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · simpa only [i, hli] using hR.le
    · simpa only [i, hri] using (le_rfl : K.cutRadius k ≤ K.cutRadius k)
  have hF := (B.inverse_smooth.contDiffAt
    (B.e.open_target.mem_nhds hcenterTarget)).differentiableAt (by simp)
  have hnonzero := n07a_actual_negativePullback_principal_ne_zero_of_fderiv_eq_closed
    h04 hz hs hcoeff.1 hcoeff.2.1 hcoeff.2.2.1 i hi hcanon hcenterD hF B.inverse_fderiv
  have hsource := n07aPhysicalRemainderSource_contDiffOn hS hT h01 hcanonical hz hs
    (n07aUnknownScalar U) ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).1
  exact n07a_tubular_physical_gluing B hcore hcoeff.1 hcoeff.2.1 hcoeff.2.2.1 hsource
    (n07aClosedPhysicalHeight_contDiffOn h04 hz hs i (J i))
    (n07aClosedPhysicalHeight_contDiffOn h04 hz hs j (J j))
    (n07aClosedPhysicalHeightGradient K x i (J i))
    (n07aClosedPhysicalHeightGradient K x j (J j))
    (fun p hp => n07aClosedPhysicalHeight_hasFDerivWithinAt h04 hz hs i (J i) hp)
    (fun p hp => n07aClosedPhysicalHeight_hasFDerivWithinAt h04 hz hs j (J j) hp)
    (fun θ => (htrace θ).1) (fun θ => (htrace θ).2)
    (n07a_closedPhysicalHeight_negative_equation h04 z hz hs i hi (hv i) (hvp i)
      (fun _ _ => n07aUnknownScalar U) f (heq i) (J i))
    (n07a_closedPhysicalHeight_negative_equation h04 z hz hs j hj (hv j) (hvp j)
      (fun _ _ => n07aUnknownScalar U) f (heq j) (J j)) hnonzero

end ContinuousFlexibility.Analysis
