import ContinuousFlexibility.Analysis.N07aNeighborhood
import ContinuousFlexibility.Analysis.N06Neighborhood

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
    N01Properties D T S C base' loss ε' :=
  n06_N01Properties_mono hT h hb he' he

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
  obtain ⟨ha, hpos, hcrit, hsym, hflow, herror, hint, hsmooth, hspatial⟩ := h
  exact ⟨fun z hz => ha z (hU hz), fun z hz => hpos z (hU hz),
    fun z hz => hcrit z (hU hz), fun z hz => hsym z (hU hz),
    fun z hz => hflow z (hU hz), fun z hz => herror z (hU hz),
    fun z hz => hint z (hU hz),
    smoothTameOn_mono hsmooth
      (((n07a_sectorNeighborhood_isOpen S base' ε' ε').prod isOpen_univ).prod isOpen_univ)
      (Set.prod_mono (Set.prod_mono (n07a_sectorNeighborhood_mono hb he)
        (subset_refl _)) (subset_refl _)),
    fun z hz => hspatial z (hU hz)⟩

theorem n07a_N04_restrict (h : N04Properties D T S C L K base loss ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    N04Properties D T S C L K base' loss ε' :=
  n06_N04Properties_mono h hb he

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
    n07a_primitiveGeometry_restrict h.1.1.1.1.1 hT h.2.2.2.2.2.1 hb he,
    n06_CanonicalPrimitiveGeometry_mono h.2.2.2.2.2.2 hb he⟩

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
