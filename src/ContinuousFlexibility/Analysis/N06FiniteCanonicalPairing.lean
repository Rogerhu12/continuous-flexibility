import ContinuousFlexibility.Analysis.N06FinitePhysicalPartition
import ContinuousFlexibility.Analysis.N06CurrentPiecePairing

/-!
# Actual compact physical tests as finite canonical pairings

The selected pieces depend only on the test's compact radial support and
the original atlas. Actual canonical representation and current-coordinate
change of variables then express the physical pairing as a finite sum in
the original L2 coordinates. Integrability is derived before summation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The height test is paired on exactly the original finite collection
of pieces meeting its physical support. -/
theorem n06_finiteCanonical_height_pairing
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    (W : CanonicalSequence S K) {η φ : PolarPoint → ℝ}
    (hrep : ∀ m, (W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m η)
    (hφ : ∀ m, MemLp (canonicalSource S K z m φ) 2 (canonicalMeasure S K m))
    (hsupport : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    IntegrableOn (fun p => η p * φ p) (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, η p * φ p) =
      ∑ m ∈ hfinite.toFinset,
        ∫ p, W m p * canonicalSource S K z m φ p ∂canonicalMeasure S K m := by
  have hpiece (m : ℕ) := n06_current_heightLpTest_pairing h04 hz hs m (W m) (hrep m) (hφ m)
  have h := n06_finitePhysicalPartition_integral h04 hz hs measurableSet_Ioc hfinite
    (fun r hr θ => by rw [hsupport r hr θ, mul_zero]) (fun m _ => (hpiece m).1)
  exact ⟨h.1, h.2.trans (Finset.sum_congr rfl fun m _ => (hpiece m).2)⟩

/-- The source test retains the actual source representative and the
same original canonical source classes on every piece. -/
theorem n06_finiteCanonical_source_pairing
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    (F : CanonicalSequence S K) {f φ : PolarPoint → ℝ}
    (hrep : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f)
    (hφ : ∀ m, MemLp (canonicalHeight S K z m φ) 2 (canonicalMeasure S K m))
    (hsupport : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    IntegrableOn (fun p => f p * φ p) (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    (∫ p in radialCore D ×ˢ Ioc (0 : ℝ) Real.pi, f p * φ p) =
      ∑ m ∈ hfinite.toFinset,
        ∫ p, F m p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m := by
  have hpiece (m : ℕ) := n06_current_sourceLpTest_pairing h04 hz hs m (F m) (hrep m) (hφ m)
  have h := n06_finitePhysicalPartition_integral h04 hz hs measurableSet_Ioc hfinite
    (fun r hr θ => by rw [hsupport r hr θ, mul_zero]) (fun m _ => (hpiece m).1)
  exact ⟨h.1, h.2.trans (Finset.sum_congr rfl fun m _ => (hpiece m).2)⟩

end ContinuousFlexibility.Statements
