import ContinuousFlexibility.Statements.N07aRegularity
import ContinuousFlexibility.Analysis.N07aNeighborhood

/-!
# Restricting the actual N07a intermediate conclusions

Only the low-order neighborhood is changed. All inverse maps, source
classes and estimates remain those already proved on the larger domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
  {base base' : ℕ} {ε ε' : ℝ}

theorem n07a_angularProperties_restrict
    (h : N07aAngularProperties S C K V b B P base ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    N07aAngularProperties S C K V b B P base' ε' := by
  let d : ℕ := h.choose
  have hd := h.choose_spec
  refine ⟨d, fun t s => ?_⟩
  let Cts : ℝ := (hd t s).choose
  have hCts : 0 < Cts := (hd t s).choose_spec.1
  have hbound := (hd t s).choose_spec.2
  exact ⟨Cts, hCts, fun z hz =>
    hbound z (n07a_sectorNeighborhood_mono (S := S) hb he hz)⟩

theorem n07a_scalarLinearInverse_restrict {G : ScalarInverseData S}
    (h : ScalarLinearInverseProperties D S C L G base ε)
    (hb : base ≤ base') (he : ε' ≤ ε) :
    ScalarLinearInverseProperties D S C L G base' ε' := by
  refine ⟨fun z hz => h.1 z (n07a_stateNeighborhood_mono (S := S) (C := C) hb he hz),
    fun z hz => h.2.1 z (n07a_stateNeighborhood_mono (S := S) (C := C) hb he hz), ?_⟩
  let loss : ℕ := h.2.2.choose
  let low : ℕ := h.2.2.choose_spec.choose
  have ht := h.2.2.choose_spec.choose_spec
  refine ⟨loss, low, fun s hs => ?_⟩
  let C0 : ℝ := (ht s hs).choose
  have hC0 : 0 ≤ C0 := (ht s hs).choose_spec.1
  have hbound := (ht s hs).choose_spec.2
  exact ⟨C0, hC0, fun z hz =>
    hbound z (n07a_sectorNeighborhood_mono (S := S) hb he hz)⟩

end ContinuousFlexibility.Analysis
