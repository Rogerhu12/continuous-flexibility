import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.StateKappaBounds
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Restricting the common nonlinear neighborhood

The relative perturbation is estimated on a smaller neighborhood and may
require a higher low order.  Every property already constructed through N05
is retained on that same neighborhood.  No change of the canonical charts,
the source spaces, or the reference graph is involved.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n06_stateNeighborhood_mono {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' : ℕ} {ε ε' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨(solve_stateGrading_monotone S hb (z.1 - C.referenceState)).trans_lt
    (hz.1.trans_le hε), hz.2.trans_le hε⟩

theorem n06_sectorNeighborhood_mono {S : PhysicalSpacesData}
    {base base' : ℕ} {ε ε' q q' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) (hq : q' ≤ q) :
    sectorNeighborhood S base' ε' q' ⊆ sectorNeighborhood S base ε q := by
  intro z hz
  exact ⟨(solve_sectorGrading_monotone S hb z.1).trans_lt
    (hz.1.trans_le hε), hz.2.trans_le hq⟩

theorem n06_isOpen_stateNeighborhood (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    IsOpen (stateNeighborhood S C base ε) := by
  exact (isOpen_lt (((solve_stateGrading_withSeminorms S).continuous_seminorm base).comp
    (continuous_fst.sub continuous_const)) continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)

theorem n06_isOpen_sectorNeighborhood (S : PhysicalSpacesData)
    (base : ℕ) (ε q : ℝ) : IsOpen (sectorNeighborhood S base ε q) := by
  exact (isOpen_lt (((solve_sectorGrading_withSeminorms S).continuous_seminorm base).comp
    continuous_fst) continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)

theorem n06_oneHighVariationWeight_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {base base' high high' : ℕ}
    (hb : base ≤ base') (hh : high ≤ high') {k : ℕ} (x : E) (v : Fin k → E) :
    oneHighVariationWeight p base high x v ≤
      oneHighVariationWeight p base' high' x v := by
  simpa only [tameJetSize, oneHighVariationWeight, Nat.zero_add] using
    (tameJetSize_mono hp hh hb k 0 x v)

theorem n06_N01Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    N01Properties D T S C base' loss ε' := by
  rcases h with ⟨hRef, _, hstate, hcontrol, hshift, hcontrolBounds, hflow,
    hleft, hreturn, hgeometry, hfixed, hcoefficient, hflowJet⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  have hopen := n06_isOpen_stateNeighborhood S C base' ε'
  have hpair : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  obtain ⟨_, hprofile⟩ := hRef.1
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hprofile.2.1 m
  have hH (m : ℕ) : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  have hE (m : ℕ) : 0 < T.E0 (T.sample m) := (hT.2.1 _ (hsample m)).2.2.1
  refine ⟨hRef, hε', hstate, hcontrol, hshift, hcontrolBounds,
    (fun z hz => hflow z (hU hz)), (fun z hz => hleft z (hU hz)),
    (fun z hz => hreturn z (hU hz)), (fun z hz => hgeometry z (hU hz)),
    (fun z hz => hfixed z (hU hz)), ?_, ?_⟩
  · intro k s
    obtain ⟨B, hB, hJ⟩ := hcoefficient k s
    refine ⟨B, hB, ?_⟩
    intro m i a b p hab hp
    obtain ⟨J, hbound⟩ := hJ m i a b p hab hp
    refine ⟨smoothDirectionsRestrict J hopen hU, ?_⟩
    intro z hz v
    change |J.D k z v| ≤ _
    exact (hbound z (hU hz) v).trans (mul_le_mul_of_nonneg_left
      (n06_oneHighVariationWeight_mono hpair hb le_rfl _ v)
      (mul_nonneg (mul_nonneg hB.le (Real.rpow_pos_of_pos (hH m) _).le)
        (Real.rpow_pos_of_pos (hE m) _).le))
  · intro k s
    obtain ⟨B, hB, hJ⟩ := hflowJet k s
    refine ⟨B, hB, ?_⟩
    intro m a b p hab hp
    obtain ⟨J, hbound⟩ := hJ m a b p hab hp
    refine ⟨smoothDirectionsRestrict J hopen hU, ?_⟩
    intro z hz v
    change min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤ _
    exact (hbound z (hU hz) v).trans (mul_le_mul_of_nonneg_left
      (n06_oneHighVariationWeight_mono hpair hb le_rfl _ v)
      (mul_nonneg (mul_nonneg hB.le (Real.rpow_pos_of_pos (hH (C.cell m)) _).le)
        (Real.rpow_pos_of_pos (hE (C.cell m)) _).le))

theorem n06_N02Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {base base' : ℕ} {ε ε' : ℝ}
    (h : N02Properties D T S C R base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N02Properties D T S C R base' ε' := by
  rcases h with ⟨hflow, hresidual, hzero, hlinear, herror, hincrement,
    hderivative, hright, hleft, hinverseTame, hresidualTame⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  refine ⟨(fun z hz => hflow z (hU hz)), (fun z hz => hresidual z (hU hz)),
    (fun z hz => hzero z (hU hz)), hlinear, (fun z hz => herror z (hU hz)),
    (fun z hz => hincrement z (hU hz)), (fun z hz => hderivative z (hU hz)),
    hright, hleft, hinverseTame, ?_⟩
  exact smoothTameOn_mono hresidualTame (n06_isOpen_sectorNeighborhood S base' ε' ε')
    (n06_sectorNeighborhood_mono hb hε hε)

theorem n06_N03Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N03Properties D T S C R L base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N03Properties D T S C R L base' ε' := by
  rcases h with ⟨ha, hpositive, hzero, hparity, hflow, hoperator, hintegral, htame⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  refine ⟨(fun z hz => ha z (hU hz)), (fun z hz => hpositive z (hU hz)),
    (fun z hz => hzero z (hU hz)), (fun z hz => hparity z (hU hz)),
    (fun z hz => hflow z (hU hz)), (fun z hz => hoperator z (hU hz)),
    (fun z hz => hintegral z (hU hz)), ?_⟩
  exact smoothTameOn_mono htame
    (((n06_isOpen_sectorNeighborhood S base' ε' ε').prod isOpen_univ).prod isOpen_univ)
    (Set.prod_mono (Set.prod_mono (n06_sectorNeighborhood_mono hb hε hε)
      (subset_refl _)) (subset_refl _))

theorem n06_N04Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (h : N04Properties D T S C L K base loss ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N04Properties D T S C L K base' loss ε' := by
  rcases h with ⟨hopen, hsupport, hnormalization, hpieces, hpositive, hnegative,
    hcover, hcharts, hboundary, hparity, hinverseParity, hcuts, htransmission,
    hoperator, hnegativeCoefficients, hpositiveDifference, hbounds, hpairing⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  refine ⟨hopen, hsupport, (fun z hz => hnormalization z (hU hz)),
    hpieces, hpositive, hnegative, hcover, (fun z hz => hcharts z (hU hz)),
    (fun z hz => hboundary z (hU hz)), (fun z hz => hparity z (hU hz)),
    (fun z hz => hinverseParity z (hU hz)), hcuts,
    (fun z hz => htransmission z (hU hz)), (fun z hz => hoperator z (hU hz)),
    (fun z hz => hnegativeCoefficients z (hU hz)),
    (fun z hz => hpositiveDifference z (hU hz)), ?_,
    (fun z hz => hpairing z (hU hz))⟩
  intro s
  obtain ⟨B, hB, hbound⟩ := hbounds s
  exact ⟨B, hB, fun z hz => hbound z (hU hz)⟩

/-- Raising the low order and reducing the radius retains the complete
construction through N05, on the very same source space and reference graph. -/
theorem n06_NonlinearPropertiesThrough05_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough05 D T S C R L K V b B base' loss ε' := by
  rcases h with ⟨⟨⟨⟨h01, h02⟩, h03⟩, hroot, hcubic, htransmission, h04⟩, h05⟩
  exact ⟨⟨⟨⟨n06_N01Properties_mono hT h01 hb hε' hε,
    n06_N02Properties_mono h02 hb hε⟩, n06_N03Properties_mono h03 hb hε⟩,
    hroot, hcubic, htransmission, n06_N04Properties_mono h04 hb hε⟩, h05⟩

end ContinuousFlexibility.Statements
