import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction
import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Restriction of the actual N02 and N03 constructions

Shrinking the common neighborhood retains the same operators and
geometric data. The genuine directional tower is restricted to the
smaller open domain, with the original local tame estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology

theorem smoothTameOn_restrict_open
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U V : Set E} {f : E → F}
    (ht : SmoothTameOn p q U f) (hV : IsOpen V) (hVU : V ⊆ U) :
    SmoothTameOn p q V f := by
  rcases ht with ⟨J, hJ⟩
  refine ⟨J.restrict hV hVU, ?_⟩
  intro k x₀ hx₀
  obtain ⟨loss, base, ε, hε, hbound⟩ := hJ k x₀ (hVU hx₀)
  refine ⟨loss, base, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hbound s hs
  exact ⟨C, hC, fun x hx hnear v => hCs x (hVU hx) hnear v⟩

theorem sectorNeighborhood_mono (S : PhysicalSpacesData)
    {base base' : ℕ} {ε ε' q q' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) (hq : q' ≤ q) :
    sectorNeighborhood S base' ε' q' ⊆ sectorNeighborhood S base ε q := by
  intro z hz
  exact ⟨((solve_sectorGrading_monotone S hb z.1).trans_lt hz.1).trans_le hε,
    hz.2.trans_le hq⟩

theorem N02Properties.restrict_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (hR : N02Properties D T S C R base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N02Properties D T S C R base' ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  rcases hR with ⟨hI, hd, hzero, hL, he, hc, hv, hright, hleft, hlin, ht⟩
  exact ⟨fun z hz hs => hI z (hsub hz) hs,
    fun z hz hs => hd z (hsub hz) hs,
    fun z hz hs => hzero z (hsub hz) hs,
    hL,
    fun z hz hs => he z (hsub hz) hs,
    fun z hz hs => hc z (hsub hz) hs,
    fun z hz hs => hv z (hsub hz) hs,
    hright, hleft, hlin,
    smoothTameOn_restrict_open ht (sectorNeighborhood_isOpen S base' ε' ε')
      (sectorNeighborhood_mono S hb hε hε)⟩

theorem N03Properties.restrict_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base base' : ℕ} {ε ε' : ℝ}
    (hL : N03Properties D T S C R L base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N03Properties D T S C R L base' ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  rcases hL with ⟨ha, hp, hr, hsym, hf, hd, hi, ht, hspatial⟩
  refine ⟨fun z hz hs => ha z (hsub hz) hs,
    fun z hz hs => hp z (hsub hz) hs,
    fun z hz hs => hr z (hsub hz) hs,
    fun z hz hs => hsym z (hsub hz) hs,
    fun z hz hs => hf z (hsub hz) hs,
    fun z hz hs => hd z (hsub hz) hs,
    fun z hz hs => hi z (hsub hz) hs, ?_,
    fun z hz hs => hspatial z (hsub hz) hs⟩
  apply smoothTameOn_restrict_open ht
    (((sectorNeighborhood_isOpen S base' ε' ε').prod isOpen_univ).prod isOpen_univ)
  intro z hz
  exact ⟨⟨sectorNeighborhood_mono S hb hε hε hz.1.1, hz.1.2⟩, hz.2⟩

end ContinuousFlexibility.Statements
