import ContinuousFlexibility.Analysis.N06CurrentTestLp

/-!
# Integrable physical pairings of the actual current representatives

The genuine height and source factors cancel against the genuine chart
Jacobian. Thus L2 canonical fields pair integrably with physical tests
on each current physical tile. This establishes integrability before
using finite sums or subtracting physical weak identities.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n06_current_pairing_pullback
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (u f : PolarPoint → ℝ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    |planeJacobian (K.chart z m) p| *
      (canonicalHeight S K z m u (K.chart z m p) *
        canonicalSource S K z m f (K.chart z m p)) = u p * f p := by
  have hc := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hh : K.height z m p ≠ 0 := (hc.2.2.2.2.2.2.2 p hp).1.ne'
  have hj : |planeJacobian (K.chart z m) p| ≠ 0 :=
    abs_ne_zero.mpr (hc.2.2.2.2.2.2.2 p hp).2.1
  unfold canonicalHeight canonicalSource
  rw [hc.2.2.1 p hp]
  field_simp

/-- Canonical L2 integrability supplies actual physical integrability
and the exact pairing identity on the original half-period tile. -/
theorem n06_current_pairing_integrable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {u f : PolarPoint → ℝ}
    (hu : MemLp (canonicalHeight S K z m u) 2 (canonicalMeasure S K m))
    (hf : MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m)) :
    IntegrableOn (fun p => u p * f p)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    (∫ p in Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi,
      u p * f p) =
      ∫ p, canonicalHeight S K z m u p * canonicalSource S K z m f p
        ∂canonicalMeasure S K m := by
  let g : PolarPoint → ℝ := fun p =>
    canonicalHeight S K z m u p * canonicalSource S K z m f p
  have hI := (n06_canonicalChart_integrable_iff h04 hz hs m g).mp (hu.integrable_mul hf)
  have heq : (fun p => |planeJacobian (K.chart z m) p| * g (K.chart z m p)) =ᵐ[
      volume.restrict
        (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)]
      (fun p => u p * f p) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    exact n06_current_pairing_pullback h04 hz hs m u f ⟨hp.1, mem_univ _⟩
  exact ⟨hI.congr heq, (integral_congr_ae heq).symm.trans
    (n06_canonicalChart_integral h04 hz hs m g).symm⟩

/-- The actual represented height pairs with any actual transformed L2 test;
its representative need not have any pointwise regularity. -/
theorem n06_current_heightLpTest_pairing
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (W : CanonicalL2 S K m) {η φ : PolarPoint → ℝ}
    (hrep : (W : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m η)
    (hφ : MemLp (canonicalSource S K z m φ) 2 (canonicalMeasure S K m)) :
    IntegrableOn (fun p => η p * φ p)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    (∫ p in Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi,
      η p * φ p) =
      ∫ p, W p * canonicalSource S K z m φ p ∂canonicalMeasure S K m := by
  have h := n06_current_pairing_integrable h04 hz hs m
    ((memLp_congr_ae hrep).mp (Lp.memLp W)) hφ
  refine ⟨h.1, h.2.trans ?_⟩
  apply integral_congr_ae
  filter_upwards [hrep] with p hp
  rw [hp]

/-- The actual represented source pairs with any actual transformed L2 test
on the same tile, using the original source L2 class. -/
theorem n06_current_sourceLpTest_pairing
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (F : CanonicalL2 S K m) {f φ : PolarPoint → ℝ}
    (hrep : (F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f)
    (hφ : MemLp (canonicalHeight S K z m φ) 2 (canonicalMeasure S K m)) :
    IntegrableOn (fun p => f p * φ p)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    (∫ p in Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi,
      f p * φ p) =
      ∫ p, F p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m := by
  have h := n06_current_pairing_integrable h04 hz hs m
    hφ ((memLp_congr_ae hrep).mp (Lp.memLp F))
  refine ⟨by simpa only [mul_comm] using h.1, ?_⟩
  calc
    _ = ∫ p in Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi,
        φ p * f p := by simp only [mul_comm]
    _ = _ := h.2.trans (integral_congr_ae (hrep.mono fun p hp => by rw [hp, mul_comm]))

theorem n06_current_heightTest_pairing
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (W : CanonicalL2 S K m) {η φ : PolarPoint → ℝ}
    (hrep : (W : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m η)
    (hφ : ContinuousOn φ
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi)) :
    IntegrableOn (fun p => η p * φ p)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    (∫ p in Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi,
      η p * φ p) =
      ∫ p, W p * canonicalSource S K z m φ p ∂canonicalMeasure S K m :=
  n06_current_heightLpTest_pairing h04 hz hs m W hrep
    (n06_current_canonicalSource_memLp h04 hz hs m hφ)

theorem n06_current_sourceTest_pairing
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (F : CanonicalL2 S K m) {f φ : PolarPoint → ℝ}
    (hrep : (F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f)
    (hφ : ContinuousOn φ
      (Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi)) :
    IntegrableOn (fun p => f p * φ p)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    (∫ p in Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi,
      f p * φ p) =
      ∫ p, F p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m :=
  n06_current_sourceLpTest_pairing h04 hz hs m F hrep
    (n06_current_canonicalHeight_memLp h04 hz hs m hφ)

end ContinuousFlexibility.Statements
