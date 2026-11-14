module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05CanonicalAngularTransport

/-!
# Actual radial test transport

Dividing the angular source-test pullback by the genuine radial Jacobian
gives the test needed for a canonical radial weak derivative. Its compact
support lies strictly inside the actual physical piece, so the quotient
extends smoothly by zero even outside the chart.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n05CanonicalRadialTestTransport (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    (φ : PolarPoint → ℝ) : PolarPoint → ℝ := fun p =>
  n05CanonicalAngularTransport S C K m φ p /
    deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1

theorem n05CanonicalRadialTestTransport_periodic_two_pi (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : Function.Periodic φ (0, Real.pi)) :
    Function.Periodic (n05CanonicalRadialTestTransport S C K m φ) (0, 2 * Real.pi) := by
  intro p
  change n05CanonicalAngularTransport S C K m φ (p + (0, 2 * Real.pi)) /
    deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) (p + (0, 2 * Real.pi)).1 = _
  rw [n05CanonicalAngularTransport_periodic_two_pi S C K m hφ p]
  simp only [Prod.fst_add, add_zero, n05CanonicalRadialTestTransport]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
/-- On the real chart this is its orientation sign times φ divided by
the actual height. No independent Jacobian has been specified. -/
theorem n05CanonicalRadialTestTransport_eq_actual (m : ℕ) (φ : PolarPoint → ℝ)
    {p : PolarPoint} (hp : p ∈ referencePhysicalPieceOpen S K m) :
    n05CanonicalRadialTestTransport S C K m φ p =
      (|planeJacobian (K.chart (C.referenceState, 0) m) p| /
        planeJacobian (K.chart (C.referenceState, 0) m) p) *
          (φ (K.chart (C.referenceState, 0) m p) / K.height (C.referenceState, 0) m p) := by
  change n05CanonicalAngularTransport S C K m φ p /
    deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1 = _
  rw [← n05_reference_planeJacobian_radial h hcoordinates m hp,
    n05CanonicalAngularTransport_eq_actual h hcoordinates m φ hp]
  simp only [div_eq_mul_inv]
  ring

include h hcoordinates in
theorem n05CanonicalRadialTestTransport_compact_support (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ Ioo (K.physicalLeft m) (K.physicalRight m) ∧
      ∀ r, r ∉ J → ∀ θ, n05CanonicalRadialTestTransport S C K m φ (r, θ) = 0 := by
  obtain ⟨J, hJ, hJI, hzero⟩ :=
    n05CanonicalAngularTransport_compact_support h hcoordinates m hφ
  refine ⟨J, hJ, hJI, fun r hr θ => ?_⟩
  change n05CanonicalAngularTransport S C K m φ (r, θ) /
    deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) r = 0
  rw [hzero r hr θ, zero_div]

include h hcoordinates in
/-- The actual quotient is a full-period physical test. The proof uses
N04 smoothness and its genuine nonzero Jacobian on the physical piece. -/
theorem n05CanonicalRadialTestTransport_test (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    RadialTest D (n05CanonicalRadialTestTransport S C K m φ) := by
  obtain ⟨J, hJ, hJI, hzero⟩ :=
    n05CanonicalRadialTestTransport_compact_support h hcoordinates m hφ
  have ht := n05CanonicalAngularTransport_test h hcoordinates m hφ
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  have hpieces := h.2.2.2.2.1.1.referenceBounds
  have hcharts := n05_reference_charts h.2.2.2.2.1
  obtain ⟨_, _, _, _, hc, _, _, hn⟩ := hcharts hz hs m
  have hd : ContDiff ℝ ∞ (n05CanonicalRadialTestTransport S C K m φ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ referencePhysicalPieceOpen S K m
    · have hnear := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
      have hactual : ContDiffAt ℝ ∞ (fun q =>
          n05CanonicalAngularTransport S C K m φ q /
            planeJacobian (K.chart (C.referenceState, 0) m) q) p :=
        ht.1.contDiffAt.div (contDiffAt_planeJacobian (hc.contDiffAt hnear)) (hn p hp).2.1
      apply hactual.congr_of_eventuallyEq
      filter_upwards [hnear] with q hq
      change n05CanonicalAngularTransport S C K m φ q /
        deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) q.1 =
          n05CanonicalAngularTransport S C K m φ q /
            planeJacobian (K.chart (C.referenceState, 0) m) q
      rw [n05_reference_planeJacobian_radial h hcoordinates m hq]
    · have hpJ : p.1 ∉ J := fun hj => hp ⟨hJI hj, mem_univ _⟩
      have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∉ J :=
        (hJ.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hpJ
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hnear] with q hq
      exact hzero q.1 hq q.2
  exact ⟨hd, n05CanonicalRadialTestTransport_periodic_two_pi S C K m hφ.2.1,
    J, hJ, fun r hr => (hpieces m).2.2 (hJI hr), hzero⟩

end ContinuousFlexibility.Statements
