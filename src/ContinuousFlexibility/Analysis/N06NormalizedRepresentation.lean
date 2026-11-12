import ContinuousFlexibility.Analysis.N06PhysicalNormalization
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Actual current representatives with the original physical normalization

On the fixed normalization region the current inverse chart is exactly the
reference inverse chart. An existing normalized reference representative can
therefore be retained on that region while reconstructing the canonical L²
unknown elsewhere. This proves representation and the physical row on the
same N05 graph; the current distributional equation remains a separate claim.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n06_inverseChart_on_normalization
    (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m : ℕ} {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (hpN : (K.inverseChart z m p).1 ∈ K.normalizationRegion) :
    K.inverseChart z m p = K.inverseChart (C.referenceState, 0) m p ∧
      K.height z m (K.inverseChart z m p) =
        K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) := by
  have hcharts := hN04.1.charts
  have hc := hcharts z hz hs m
  have hr := hcharts (C.referenceState, 0) href hsector m
  have hphys := hc.2.1 hp
  have hnormalization := hN04.1.normalization z hz hs m
  have hphys0 : K.inverseChart z m p ∈ physicalPieceOpen S K (C.referenceState, 0) m := by
    have hmem : K.inverseChart z m p ∈ physicalPieceOpen S K z m ∩
        (K.normalizationRegion ×ˢ (univ : Set ℝ)) := ⟨hphys, hpN, mem_univ _⟩
    rw [hnormalization.1] at hmem
    exact hmem.1
  have hnorm := hnormalization.2 (K.inverseChart z m p) hphys hpN
  have hi : K.inverseChart z m p = K.inverseChart (C.referenceState, 0) m p := by
    calc
      K.inverseChart z m p = K.inverseChart (C.referenceState, 0) m
          (K.chart (C.referenceState, 0) m (K.inverseChart z m p)) :=
        (hr.2.2.1 _ hphys0).symm
      _ = K.inverseChart (C.referenceState, 0) m p := by
        rw [← hnorm.1, hc.2.2.2.1 p hp]
  exact ⟨hi, hnorm.2.trans (congrArg (K.height (C.referenceState, 0) m) hi)⟩

/-- Retaining the reference representative on the fixed normalization
region does not alter the actual current canonical unknown. -/
theorem n06_exists_normalized_physical_representation
    (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {Fref : CanonicalSequence S K}
    {ηref fref : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (C.referenceState, 0) U Fref ηref fref)
    (hrow : referenceRow D ηref = 0) (F : CanonicalSequence S K) :
    ∃ η f : PolarPoint → ℝ,
      HasCanonicalRepresentation D S C K z U F η f ∧ referenceRow D η = 0 := by
  classical
  obtain ⟨η₀, f, hrep₀, _⟩ := n06_exists_physical_representation hN04 hz hs U F
  let η : PolarPoint → ℝ := fun p =>
    if p.1 ∈ K.normalizationRegion then ηref p else η₀ p
  refine ⟨η, f, ⟨?_, hrep₀.2⟩, ?_⟩
  · intro m
    filter_upwards [hrep.1 m, hrep₀.1 m,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hpref hp₀ hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    by_cases hpN : (K.inverseChart z m p).1 ∈ K.normalizationRegion
    · have hi := n06_inverseChart_on_normalization hN04 href hsector hz hs hpc hpN
      change U.1 m p =
        (η (K.inverseChart z m p) - U.2.1 * S.chiLeft (K.inverseChart z m p).1) /
          K.height z m (K.inverseChart z m p)
      simp only [η, ite_eq_left hpN]
      rw [hi.2, hi.1]
      exact hpref
    · change U.1 m p =
        (η (K.inverseChart z m p) - U.2.1 * S.chiLeft (K.inverseChart z m p).1) /
          K.height z m (K.inverseChart z m p)
      simpa only [η, ite_eq_right hpN, canonicalHeight] using hp₀
  · have heq : referenceRow D η = referenceRow D ηref := by
      unfold referenceRow
      apply intervalIntegral.integral_congr
      intro r _
      by_cases hr : referenceColumn D r = 0
      · simp only [hr, zero_mul]
      · have hrN : r ∈ K.normalizationRegion := hN04.1.normalizationSupport (Function.mem_support.mpr hr)
        have hm : referenceMode η 2 r = referenceMode ηref 2 r := by
          unfold referenceMode
          apply congrArg (fun g : ℝ → ℝ => radialAngularMean g)
          funext θ
          simp only [η, ite_eq_left hrN]
        exact congrArg (fun x : ℝ => referenceColumn D r * x) hm
    exact heq.trans hrow

/-- Every member of the same N05 graph has actual normalized current
physical representatives for any specified canonical source. The remaining
operator task is exactly the physical weak equation. -/
theorem n06_graph_exists_normalized_representation
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hN04 : N04Properties D T S C L K base loss ε)
    (hN05 : N05Properties D T S C K V b B)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (u : B.Space) (F : CanonicalSequence S K) :
    ∃ η f : PolarPoint → ℝ,
      HasCanonicalRepresentation D S C K z u.val.1 F η f ∧ referenceRow D η = 0 := by
  have hgraph := hN05.2.2.2.2.2.2.1
  obtain ⟨_, ηref, fref, hrep, hweak⟩ := (hgraph u.val).mp u.property
  exact n06_exists_normalized_physical_representation hN04 href hsector hz hs
    hrep hweak.2.2.1 F

end ContinuousFlexibility.Statements
