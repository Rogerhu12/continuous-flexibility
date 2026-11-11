import ContinuousFlexibility.Analysis.N07aNeighborhood

/-!
# The same cumulative construction on a smaller neighborhood

All geometric functions, graph spaces and inverses are unchanged. The
original estimates restrict to a stronger fixed low norm and a smaller
positive radius; genuine derivative towers are restricted as towers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true

local instance n07aConstructionRestrictionAnnularGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := n07aNonlinearAnnularGroup S

local instance n07aConstructionRestrictionAnnularModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := n07aNonlinearAnnularModule S

local instance n07aConstructionRestrictionAnnularAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S) := n07aNonlinearAnnularAddGroup S

local instance n07aConstructionRestrictionAnnularSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := n07aNonlinearAnnularSMul S

local instance n07aConstructionRestrictionAnnularSub (S : PhysicalSpacesData) :
    Sub (AnnularState S) := n07aNonlinearAnnularSub S

local instance n07aConstructionRestrictionSectorGroup (S : PhysicalSpacesData) :
    AddCommGroup (StateDirections S) := n07aNonlinearDirectionsGroup S

local instance n07aConstructionRestrictionSectorModule (S : PhysicalSpacesData) :
    Module ℝ (StateDirections S) := n07aNonlinearDirectionsModule S

local instance n07aConstructionRestrictionSectorAddGroup (S : PhysicalSpacesData) :
    AddGroup (StateDirections S) := n07aNonlinearDirectionsAddGroup S

local instance n07aConstructionRestrictionSectorSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S) := n07aNonlinearDirectionsSMul S

local instance n07aConstructionRestrictionSectorSub (S : PhysicalSpacesData) :
    Sub (StateDirections S) := n07aNonlinearDirectionsSub S

local instance n07aConstructionRestrictionParameterGroup (S : PhysicalSpacesData) :
    AddCommGroup (StateDirections S × ℝ) := n07aNonlinearSectorParameterGroup S

local instance n07aConstructionRestrictionParameterModule (S : PhysicalSpacesData) :
    Module ℝ (StateDirections S × ℝ) := n07aNonlinearSectorParameterModule S

local instance n07aConstructionRestrictionParameterAddGroup (S : PhysicalSpacesData) :
    AddGroup (StateDirections S × ℝ) := n07aNonlinearSectorParameterAddGroup S

local instance n07aConstructionRestrictionParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S × ℝ) := n07aNonlinearSectorParameterSMul S

local instance n07aConstructionRestrictionParameterSub (S : PhysicalSpacesData) :
    Sub (StateDirections S × ℝ) := n07aNonlinearSectorParameterSub S

local instance n07aConstructionRestrictionAnnularParameterGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S × ℝ) := n07aNonlinearAnnularParameterGroup S

local instance n07aConstructionRestrictionAnnularParameterModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S × ℝ) := n07aNonlinearAnnularParameterModule S

local instance n07aConstructionRestrictionAnnularParameterAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S × ℝ) := n07aNonlinearAnnularParameterAddGroup S

local instance n07aConstructionRestrictionAnnularParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := n07aNonlinearAnnularParameterSMul S

local instance n07aConstructionRestrictionAnnularParameterSub (S : PhysicalSpacesData) :
    Sub (AnnularState S × ℝ) := n07aNonlinearAnnularParameterSub S

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base base' loss : ℕ} {ε ε' : ℝ}

theorem n07a_N01_restrict
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (he : ε' ≤ ε) (he' : 0 < ε') :
    N01Properties D T S C base' loss ε' := by
  have hU := n07a_stateNeighborhood_mono (S := S) (C := C) hb he
  have hOpen := n07a_stateNeighborhood_isOpen S C base' ε'
  have hmono : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (solve_stateGrading_monotone S) weighted_realGrading_monotone
  obtain ⟨hD, _, href, hc, hi, hcj, hflow, hleft, hinv, hbounds, hcritical,
    hcoeff, hflowj⟩ := h
  refine ⟨hD, he', href, hc, hi, hcj, fun z hz => hflow z (hU hz),
    fun z hz => hleft z (hU hz), fun z hz => hinv z (hU hz),
    fun z hz => hbounds z (hU hz), fun z hz => hcritical z (hU hz), ?_, ?_⟩
  · intro k s
    let B : ℝ := (hcoeff k s).choose
    have hB : 0 < B := (hcoeff k s).choose_spec.1
    have hBb := (hcoeff k s).choose_spec.2
    refine ⟨B, hB, fun m i a b p hab hp => ?_⟩
    let J := (hBb m i a b p hab hp).choose
    have hJ := (hBb m i a b p hab hp).choose_spec
    refine ⟨smoothDirectionsRestrict J hOpen hU, fun z hz v => ?_⟩
    have hw := n07a_oneHighVariationWeight_base_mono _ hmono hb
      (s + loss) (z - (C.referenceState, 0)) v
    have hfactor := n07a_materialSample_jetFactor_nonneg hD.1 hT hB.le m
    have hfactor' : 0 ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample m) ^ B := by
      convert hfactor using 1
      ring
    exact (hJ z (hU hz) v).trans (mul_le_mul_of_nonneg_left hw hfactor')
  · intro k s
    let B : ℝ := (hflowj k s).choose
    have hB : 0 < B := (hflowj k s).choose_spec.1
    have hBb := (hflowj k s).choose_spec.2
    refine ⟨B, hB, fun m a b p hab hp => ?_⟩
    let J := (hBb m a b p hab hp).choose
    have hJ := (hBb m a b p hab hp).choose_spec
    refine ⟨smoothDirectionsRestrict J hOpen hU, fun z hz v => ?_⟩
    have hw := n07a_oneHighVariationWeight_base_mono _ hmono hb
      (s + loss) (z - (C.referenceState, 0)) v
    have hfactor := n07a_materialSample_jetFactor_nonneg hD.1 hT hB.le (C.cell m)
    have hfactor' : 0 ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B := by
      convert hfactor using 1
      ring
    exact (hJ z (hU hz) v).trans (mul_le_mul_of_nonneg_left hw hfactor')

theorem n07a_N02_restrict (h : N02Properties D T S C R base ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    N02Properties D T S C R base' ε' := by
  have hU := n07a_stateNeighborhood_mono (S := S) (C := C) hb he
  obtain ⟨hinv, hdecode, hzero, hlinear, herror, hincrement, hderiv,
    hright, hleft, htame, hsmooth⟩ := h
  exact ⟨fun z hz => hinv z (hU hz), fun z hz => hdecode z (hU hz),
    fun z hz => hzero z (hU hz), hlinear, fun z hz => herror z (hU hz),
    fun z hz => hincrement z (hU hz), fun z hz => hderiv z (hU hz),
    hright, hleft, htame,
    smoothTameOn_mono hsmooth (n07a_sectorNeighborhood_isOpen S base' ε' ε')
      (n07a_sectorNeighborhood_mono hb he)⟩

theorem n07a_N03_restrict (h : N03Properties D T S C R L base ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    N03Properties D T S C R L base' ε' := by
  have hU := n07a_stateNeighborhood_mono (S := S) (C := C) hb he
  obtain ⟨ha, hpos, hcrit, hsym, hflow, herror, hint, hsmooth⟩ := h
  exact ⟨fun z hz => ha z (hU hz), fun z hz => hpos z (hU hz),
    fun z hz => hcrit z (hU hz), fun z hz => hsym z (hU hz),
    fun z hz => hflow z (hU hz), fun z hz => herror z (hU hz),
    fun z hz => hint z (hU hz),
    smoothTameOn_mono hsmooth
      (((n07a_sectorNeighborhood_isOpen S base' ε' ε').prod isOpen_univ).prod isOpen_univ)
      (Set.prod_mono (Set.prod_mono (n07a_sectorNeighborhood_mono hb he)
        (subset_refl _)) (subset_refl _))⟩

theorem n07a_N04_restrict (h : N04Properties D T S C L K base loss ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    N04Properties D T S C L K base' loss ε' := by
  have hU := n07a_stateNeighborhood_mono (S := S) (C := C) hb he
  obtain ⟨hregion, hsupport, hfrozen, hinterval, hpos, hneg, hcover,
    hchart, hboundary, hsym, hinvsym, hcut, htrace, hop, hnegative,
    hdivided, hjets, hpair⟩ := h
  refine ⟨hregion, hsupport, fun z hz => hfrozen z (hU hz), hinterval, hpos, hneg,
    hcover, fun z hz => hchart z (hU hz), fun z hz => hboundary z (hU hz),
    fun z hz => hsym z (hU hz), fun z hz => hinvsym z (hU hz), hcut,
    fun z hz => htrace z (hU hz), fun z hz => hop z (hU hz),
    fun z hz => hnegative z (hU hz), fun z hz => hdivided z (hU hz), ?_,
    fun z hz => hpair z (hU hz)⟩
  intro s
  obtain ⟨B, hB, hBb⟩ := hjets s
  exact ⟨B, hB, fun z hz => hBb z (hU hz)⟩

theorem n07a_through03_restrict
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hb : base ≤ base') (he : ε' ≤ ε) (he' : 0 < ε') :
    NonlinearPropertiesThrough03 D T S C R L base' loss ε' :=
  ⟨⟨n07a_N01_restrict hT h.1.1 hb he he', n07a_N02_restrict h.1.2 hb he⟩,
    n07a_N03_restrict h.2 hb he⟩

theorem n07a_through04_restrict
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hb : base ≤ base') (he : ε' ≤ ε) (he' : 0 < ε') :
    NonlinearPropertiesThrough04 D T S C R L K base' loss ε' :=
  ⟨n07a_through03_restrict hT h.1 hb he he', h.2.1, h.2.2.1, h.2.2.2.1,
    n07a_N04_restrict h.2.2.2.2.1 hb he,
    n07a_primitiveGeometry_restrict h.1.1.1.1.1 hT h.2.2.2.2.2 hb he⟩

variable {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B}

theorem n07a_N06_restrict (h : N06Properties D S C K L V b B P base ε)
    (hb : base ≤ base') (he : ε' ≤ ε) (he' : 0 < ε') :
    N06Properties D S C K L V b B P base' ε' :=
  ⟨he', fun z hz => h.2 z (n07a_stateNeighborhood_mono hb he hz)⟩

theorem n07a_through06_restrict
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough06 D T S C R L K V b B P base loss ε)
    (hb : base ≤ base') (he : ε' ≤ ε) (he' : 0 < ε') :
    NonlinearPropertiesThrough06 D T S C R L K V b B P base' loss ε' :=
  ⟨⟨n07a_through04_restrict hT h.1.1 hb he he', h.1.2⟩,
    n07a_N06_restrict h.2 hb he he'⟩

end ContinuousFlexibility.Analysis
