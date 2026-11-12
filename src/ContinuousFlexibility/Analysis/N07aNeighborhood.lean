import ContinuousFlexibility.Analysis.N07aParameterGrading
import ContinuousFlexibility.Analysis.N07aForwardCoefficients
import ContinuousFlexibility.Analysis.TameTransfer
import ContinuousFlexibility.Statements.N07aCanonicalGeometry

/-!
# Restricting the actual construction to a stronger neighborhood

The original functions and genuine directional derivatives are retained.
Increasing the fixed low order and decreasing the radius only restrict
their domain and increases the low variation bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true

local instance n07aNeighborhoodAnnularGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := n07aNonlinearAnnularGroup S

local instance n07aNeighborhoodAnnularModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := n07aNonlinearAnnularModule S

local instance n07aNeighborhoodAnnularAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S) := n07aNonlinearAnnularAddGroup S

local instance n07aNeighborhoodAnnularSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := n07aNonlinearAnnularSMul S

local instance n07aNeighborhoodAnnularSub (S : PhysicalSpacesData) :
    Sub (AnnularState S) := n07aNonlinearAnnularSub S

local instance n07aNeighborhoodSectorGroup (S : PhysicalSpacesData) :
    AddCommGroup (StateDirections S) := n07aNonlinearDirectionsGroup S

local instance n07aNeighborhoodSectorModule (S : PhysicalSpacesData) :
    Module ℝ (StateDirections S) := n07aNonlinearDirectionsModule S

local instance n07aNeighborhoodSectorAddGroup (S : PhysicalSpacesData) :
    AddGroup (StateDirections S) := n07aNonlinearDirectionsAddGroup S

local instance n07aNeighborhoodSectorSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S) := n07aNonlinearDirectionsSMul S

local instance n07aNeighborhoodSectorSub (S : PhysicalSpacesData) :
    Sub (StateDirections S) := n07aNonlinearDirectionsSub S

local instance n07aNeighborhoodParameterGroup (S : PhysicalSpacesData) :
    AddCommGroup (StateDirections S × ℝ) := n07aNonlinearSectorParameterGroup S

local instance n07aNeighborhoodParameterModule (S : PhysicalSpacesData) :
    Module ℝ (StateDirections S × ℝ) := n07aNonlinearSectorParameterModule S

local instance n07aNeighborhoodParameterAddGroup (S : PhysicalSpacesData) :
    AddGroup (StateDirections S × ℝ) := n07aNonlinearSectorParameterAddGroup S

local instance n07aNeighborhoodParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S × ℝ) := n07aNonlinearSectorParameterSMul S

local instance n07aNeighborhoodParameterSub (S : PhysicalSpacesData) :
    Sub (StateDirections S × ℝ) := n07aNonlinearSectorParameterSub S

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base base' : ℕ} {ε ε' : ℝ}

theorem n07a_stateNeighborhood_mono (hb : base ≤ base') (he : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨(solve_stateGrading_monotone S hb _).trans_lt (hz.1.trans_le he),
    hz.2.trans_le he⟩

theorem n07a_sectorNeighborhood_mono (hb : base ≤ base') (he : ε' ≤ ε) :
    sectorNeighborhood S base' ε' ε' ⊆ sectorNeighborhood S base ε ε := by
  intro z hz
  exact ⟨(solve_sectorGrading_monotone S hb _).trans_lt (hz.1.trans_le he),
    hz.2.trans_le he⟩

theorem n07a_stateNeighborhood_isOpen (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    IsOpen (stateNeighborhood S C base ε) :=
  (isOpen_lt
    (((solve_stateGrading_withSeminorms S).continuous_seminorm base).comp
      (continuous_fst.sub continuous_const)) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

theorem n07a_oneHighVariationWeight_base_mono
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    {base base' : ℕ} (hb : base ≤ base') (high : ℕ)
    (x : E) {k : ℕ} (v : Fin k → E) :
    oneHighVariationWeight p base high x v ≤
      oneHighVariationWeight p base' high x v := by
  exact tameJetSize_mono hp (show 0 ≤ 0 from le_rfl) hb k high x v

theorem n07a_materialSample_jetFactor_nonneg
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    0 ≤ B * T.E0 (T.sample m) ^ B * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have hp := hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 m)
  exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hp.2.2.1.le _))
    (Real.rpow_nonneg hp.2.1.le _)

private def n07aNeighborhoodParameterSize (S : PhysicalSpacesData)
    (s : ℕ) (z : CanonicalGeometry.Parameter S) : ℝ :=
  CanonicalGeometry.parameterGrading S s z

private def n07aNeighborhoodVariation (S : PhysicalSpacesData) (base high : ℕ)
    (z : CanonicalGeometry.Parameter S) {k : ℕ}
    (v : Fin k → CanonicalGeometry.Parameter S) : ℝ :=
  oneHighVariationWeight (CanonicalGeometry.parameterGrading S) base high z v

private def n07aGeometryZeroBounds (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z ∈ sectorNeighborhood S base ε ε,
    ∀ m a (p : CanonicalGeometry.unitStrip) i j, i + j ≤ s →
      |CanonicalGeometry.differenceJets D T S C L K z a m i j p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          n07aNeighborhoodParameterSize S (s + loss) z

private theorem n07aGeometryZeroBounds_restrict {loss : ℕ}
    (h : n07aGeometryZeroBounds D T S C L K base loss ε)
    (hU : sectorNeighborhood S base' ε' ε' ⊆ sectorNeighborhood S base ε ε) :
    n07aGeometryZeroBounds D T S C L K base' loss ε' := by
  intro s
  let B : ℝ := (h s).choose
  refine ⟨B, (h s).choose_spec.1, ?_⟩
  intro z hz
  exact (h s).choose_spec.2 z (hU hz)

private def n07aGeometryTowerBounds (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (base : ℕ) (ε : ℝ)
    (d : ∀ k : ℕ, CanonicalGeometry.Parameter S →
      (Fin k → CanonicalGeometry.Parameter S) → CanonicalGeometry.JetField) : Prop :=
  ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → CanonicalGeometry.Parameter S,
      ∀ m a (p : CanonicalGeometry.unitStrip) i j, i + j ≤ s →
        |d k z v a m i j p| ≤
          B * T.E0 (T.sample (K.cell m)) ^ B * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
            n07aNeighborhoodVariation S base (s + loss) z v

private theorem n07aGeometryTowerBounds_restrict
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {d : ∀ k : ℕ, CanonicalGeometry.Parameter S →
      (Fin k → CanonicalGeometry.Parameter S) → CanonicalGeometry.JetField}
    (h : n07aGeometryTowerBounds T S K base ε d)
    (hb : base ≤ base')
    (hU : sectorNeighborhood S base' ε' ε' ⊆ sectorNeighborhood S base ε ε) :
    n07aGeometryTowerBounds T S K base' ε' d := by
  intro k
  let loss : ℕ := (h k).choose
  have hJs := (h k).choose_spec
  refine ⟨loss, fun s => ?_⟩
  let B : ℝ := (hJs s).choose
  have hB : 0 < B := (hJs s).choose_spec.1
  have hBb := (hJs s).choose_spec.2
  refine ⟨B, hB, fun z hz v m a p i j hij => ?_⟩
  have hw := n07a_oneHighVariationWeight_base_mono
    (n07aParameterGrading S) (n07aParameterGrading_monotone S) hb (s + loss) z v
  exact (hBb z (hU hz) v m a p i j hij).trans
    (mul_le_mul_of_nonneg_left hw
      (n07a_materialSample_jetFactor_nonneg hD hT hB.le (K.cell m)))

/-- The new tower is the actual old tower restricted to the smaller open
 domain. In particular no parameter derivative is replaced by a bound. -/
theorem n07a_currentJets_restrict
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    CanonicalGeometry.CurrentJets D T S C L K base' ε' := by
  have hU := n07a_sectorNeighborhood_mono (S := S) hb he
  refine ⟨fun z hz => hcur.1 z (hU hz), ?_, ?_⟩
  · exact ⟨hcur.2.1.choose,
      n07aGeometryZeroBounds_restrict hcur.2.1.choose_spec hU⟩
  · let J := hcur.2.2.choose
    have hJ := hcur.2.2.choose_spec
    let J' : SmoothDirections (sectorNeighborhood S base' ε' ε')
        (CanonicalGeometry.differenceJets D T S C L K) :=
      smoothDirectionsRestrict (E := StateDirections S × ℝ)
        (F := CanonicalGeometry.JetField) J
        (n07a_sectorNeighborhood_isOpen S base' ε' ε') hU
    exact ⟨J', n07aGeometryTowerBounds_restrict hD hT hJ hb hU⟩

theorem n07a_transmissionParameter_restrict
    (hb : base ≤ base') (he : ε' ≤ ε) {z : AnnularState S × ℝ}
    (hz : CanonicalGeometry.TransmissionParameter S C base' ε' z) :
    CanonicalGeometry.TransmissionParameter S C base ε z := by
  rcases hz with hr | ⟨hz, hs⟩
  · exact Or.inl hr
  · exact Or.inr ⟨n07a_stateNeighborhood_mono hb he hz, hs⟩

theorem n07a_transmissionGeometry_restrict
    (h : CanonicalGeometry.TransmissionGeometry D S C K base ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    CanonicalGeometry.TransmissionGeometry D S C K base' ε' := by
  refine ⟨h.1, ?_, ?_⟩
  · intro i j hij hadj hroot
    obtain ⟨ei, ej, si, sj, hei, hej, hsi, hsj, hjets⟩ := h.2.1 i j hij hadj hroot
    exact ⟨ei, ej, si, sj, hei, hej, hsi, hsj,
      fun z hz θ => hjets z (n07a_transmissionParameter_restrict hb he hz) θ⟩
  · intro k z hz θ
    exact h.2.2 k z (n07a_transmissionParameter_restrict hb he hz) θ

theorem n07a_primitiveGeometry_restrict
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : CanonicalGeometry.PrimitiveGeometryProperties D T S C L K base ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    CanonicalGeometry.PrimitiveGeometryProperties D T S C L K base' ε' :=
  ⟨h.1, h.2.1, h.2.2.1, n07a_currentJets_restrict hD hT h.2.2.2.1 hb he,
    h.2.2.2.2.1, n07a_transmissionGeometry_restrict h.2.2.2.2.2 hb he⟩

end ContinuousFlexibility.Analysis
