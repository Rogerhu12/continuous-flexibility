import ContinuousFlexibility.Analysis.N06PhysicalPeriodicity

/-!
# The fixed physical normalization row under reconstruction

N04 fixes the actual chart and height on the support of the reference
column. Reconstructing the same canonical unknown at two states therefore
leaves the physical normalization row unchanged. This argument is pointwise
on that support and does not assume a differential equation for the unknown.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The actual reconstructed height, including its left constant tail. -/
def n06PhysicalHeight (K : CanonicalData S) (z : AnnularState S × ℝ)
    (W : ℕ → PolarPoint → ℝ) (aL : ℝ) (p : PolarPoint) : ℝ :=
  n06PhysicalReconstruct K z W (K.height z) p + aL * S.chiLeft p.1

theorem n06PhysicalHeight_periodic
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (W : ℕ → PolarPoint → ℝ) (aL : ℝ) :
    Function.Periodic (n06PhysicalHeight K z W aL) (0, Real.pi) := by
  have hcharts := hN04.2.2.2.2.2.2.2.1
  have hperiod := n06PhysicalReconstruct_periodic hN04 hz hs W (K.height z)
    (fun m p hp => ((hcharts z hz hs m).2.2.2.2.2.2.2 p hp).2.2.2)
  intro p
  simp only [n06PhysicalHeight, hperiod p, Prod.fst_add, add_zero]

/-- The reference normalization region is fixed pointwise for arbitrary
canonical representatives, including the zero extension off the piece cover. -/
theorem n06PhysicalHeight_on_normalization
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (W : ℕ → PolarPoint → ℝ) (aL : ℝ)
    {p : PolarPoint} (hpN : p.1 ∈ K.normalizationRegion) :
    n06PhysicalHeight K z W aL p =
      n06PhysicalHeight K (C.referenceState, 0) W aL p := by
  classical
  by_cases hex : ∃ m, p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
  · obtain ⟨m, hm⟩ := hex
    have hp : p ∈ physicalPieceOpen S K m := ⟨hm, mem_univ _⟩
    have hnormal := hN04.2.2.1 z hz hs m p hp hpN
    simp only [n06PhysicalHeight]
    rw [n06PhysicalReconstruct_on_piece hN04 z W (K.height z) hp,
      n06PhysicalReconstruct_on_piece hN04 (C.referenceState, 0) W
        (K.height (C.referenceState, 0)) hp, hnormal.1, hnormal.2]
  · simp only [n06PhysicalHeight, n06PhysicalReconstruct, ite_eq_right hex]

/-- The normalization row is identical to its value at the reference state;
no change of representative or unproved transmission rule is used here. -/
theorem n06PhysicalHeight_referenceRow
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (W : ℕ → PolarPoint → ℝ) (aL : ℝ) :
    referenceRow D (n06PhysicalHeight K z W aL) =
      referenceRow D (n06PhysicalHeight K (C.referenceState, 0) W aL) := by
  unfold referenceRow
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : referenceColumn D r = 0
  · simp only [hr, zero_mul]
  · have hrN : r ∈ K.normalizationRegion := hN04.2.1 (Function.mem_support.mpr hr)
    have hm : referenceMode (n06PhysicalHeight K z W aL) 2 r =
        referenceMode (n06PhysicalHeight K (C.referenceState, 0) W aL) 2 r := by
      unfold referenceMode
      apply congrArg (fun g : ℝ → ℝ => radialAngularMean g)
      funext θ
      rw [n06PhysicalHeight_on_normalization hN04 hz hs W aL hrN]
    exact congrArg (fun x : ℝ => referenceColumn D r * x) hm

end ContinuousFlexibility.Statements
