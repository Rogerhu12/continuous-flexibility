import ContinuousFlexibility.Analysis.N05ReferenceSymbolClosure

/-!
# Period and reflection identities on the closed canonical pieces

N04 specifies these identities in the open physical pieces.  Its actual
closed-piece smoothness extends them to both endpoints for every admitted
state, without imposing any values on the inverse chart at the endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n05_canonical_closed_periodicity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) ∧
      K.height z m (p + (0, Real.pi)) = K.height z m p := by
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, hcharts, hclosed, _⟩
  obtain ⟨_, _, _, _, _, _, _, hperiodic⟩ := hcharts z hz hs m
  have hshift (q : PolarPoint)
      (hq : q.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      (q + (0, Real.pi)).1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) := by
    simpa only [Prod.fst_add, add_zero] using hq
  constructor
  · apply n05_eqOn_closed_strip_of_nonreflection (hpieces m).1
      (f := fun q => K.chart z m (q + (0, Real.pi)))
      (g := fun q => K.chart z m q + (0, Real.pi)) _ _ _ p hp
    · intro q hq
      exact (hclosed z hz hs m (q + (0, Real.pi)) (hshift q hq)).1.continuousAt.comp
        (f := fun r : PolarPoint => r + (0, Real.pi))
        (continuousAt_id.add continuousAt_const)
    · intro q hq
      exact (hclosed z hz hs m q hq).1.continuousAt.add continuousAt_const
    · intro q hq _
      exact (hperiodic q ⟨hq, mem_univ _⟩).2.2.1
  · apply n05_eqOn_closed_strip_of_nonreflection (hpieces m).1
      (f := fun q => K.height z m (q + (0, Real.pi)))
      (g := K.height z m) _ _ _ p hp
    · intro q hq
      exact (hclosed z hz hs m (q + (0, Real.pi)) (hshift q hq)).2.1.continuousAt.comp
        (f := fun r : PolarPoint => r + (0, Real.pi))
        (continuousAt_id.add continuousAt_const)
    · intro q hq
      exact (hclosed z hz hs m q hq).2.1.continuousAt
    · intro q hq _
      exact (hperiodic q ⟨hq, mem_univ _⟩).2.2.2

theorem n05_canonical_closed_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.chart z m (p.1, -p.2) = ((K.chart z m p).1, -(K.chart z m p).2) ∧
      K.height z m (p.1, -p.2) = K.height z m p := by
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, _, hclosed, hreflection, _⟩
  constructor
  · apply n05_eqOn_closed_strip_of_nonreflection (hpieces m).1
      (f := fun q => K.chart z m (q.1, -q.2))
      (g := fun q => ((K.chart z m q).1, -(K.chart z m q).2)) _ _ _ p hp
    · intro q hq
      exact (hclosed z hz hs m (q.1, -q.2) hq).1.continuousAt.comp
        (f := fun r : PolarPoint => (r.1, -r.2))
        (continuousAt_fst.prodMk continuousAt_snd.neg)
    · intro q hq
      have hqChart := (hclosed z hz hs m q hq).1.continuousAt
      exact hqChart.fst.prodMk hqChart.snd.neg
    · intro q hq _
      exact (hreflection z hz hs m q ⟨hq, mem_univ _⟩).1
  · apply n05_eqOn_closed_strip_of_nonreflection (hpieces m).1
      (f := fun q => K.height z m (q.1, -q.2))
      (g := K.height z m) _ _ _ p hp
    · intro q hq
      exact (hclosed z hz hs m (q.1, -q.2) hq).2.1.continuousAt.comp
        (f := fun r : PolarPoint => (r.1, -r.2))
        (continuousAt_fst.prodMk continuousAt_snd.neg)
    · intro q hq
      exact (hclosed z hz hs m q hq).2.1.continuousAt
    · intro q hq _
      exact (hreflection z hz hs m q ⟨hq, mem_univ _⟩).2.1

end ContinuousFlexibility.Statements

