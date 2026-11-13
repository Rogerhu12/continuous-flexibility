import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
import ContinuousFlexibility.Analysis.N04RealizationFixedSpatialProduct
import ContinuousFlexibility.Analysis.N04RealizationJetScalars
import ContinuousFlexibility.Analysis.N04SourceColumnsProduct
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Reference data and genuine towers for source-column operations

The reference predicate is the scalar-family version of `ReferenceJets`.
The conversion lemmas retain the actual spatial derivatives and the
sample of each piece. Positive parameter derivatives retain the sampled
height gain; only the zeroth derivative contains the reference field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

/-- A scalar reference family on the unit strip, with the same sample
and coefficient envelope as the frozen reference-jet clause. -/
def N04SourceReferenceData (T : MaterialData) (cell : ℕ → ℕ)
    (f₀ : ℕ → PolarPoint → ℝ) : Prop :=
  (∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip ∧
    ∀ q ∈ unitStrip, f₀ m (q + (0, Real.pi)) = f₀ m q) ∧
  ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m q, q ∈ unitStrip → ∀ i j : ℕ,
    i + j ≤ s → |mixedDerivative i j (f₀ m) q| ≤
      B * T.E0 (T.sample (cell m)) ^ B

section Bridges

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {base : ℕ} {ε : ℝ} {f : Parameter S → ℕ → PolarPoint → ℝ}
  {f₀ : ℕ → PolarPoint → ℝ}

/-- A reference atom has scalar reference data. -/
theorem n04SourceReferenceData_of_referenceJets
    {D : ReferenceData} {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} (h : ReferenceJets D T S C L K) (a : Atom) :
    N04SourceReferenceData T K.cell (fun m => atom D T S C L K (C.referenceState, 0) m a) :=
  ⟨fun m => h.1 m a, fun s => ⟨(h.2 s).choose, (h.2 s).choose_spec.1,
    fun m q hq i j hij => (h.2 s).choose_spec.2 m a q hq i j hij⟩⟩

/-- The supplied difference tower is the tower of the actual spatial
difference, before any estimate or product is formed. -/
def CurrentJetDataOn.sourceColumns_differenceRegularity
    (h : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀) (m : ℕ) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z q => f z m q - f₀ m q) where
  spatial z hz := (h.1 z hz m trivial).1.sub (h₀.1 m).1
  parameter i j q hq := h.2.choose m i j ⟨q, hq⟩

/-- Adding back the fixed reference field reconstructs a genuine tower
of the current field itself. -/
def CurrentJetDataOn.sourceColumns_regularity
    (h : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀) (m : ℕ) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun z => f z m) where
  spatial z hz := (h.1 z hz m trivial).1
  parameter i j q hq :=
    (smoothDirectionsAdd (h.2.choose m i j ⟨q, hq⟩)
      (smoothDirections_constant (isOpen_sectorNeighborhood S base ε ε)
        (mixedDerivative i j (f₀ m) q))).congr (fun z hz => by
      rw [mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (h.1 z hz m trivial).1 (h₀.1 m).1 i j hq]
      exact sub_add_cancel _ _)

/-- Every positive parameter derivative of the full field is the same
as the derivative of its reference difference. -/
theorem CurrentJetDataOn.sourceColumns_positive_jet_eq
    (h : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀)
    (m i j : ℕ) (q : unitStrip)
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative i j (f z m) q.val))
    {k : ℕ} (hk : 0 < k) {z : Parameter S}
    (hz : z ∈ sectorNeighborhood S base ε ε) (v : Fin k → Parameter S) :
    J.D k z v = (h.2.choose m i j q).D k z v := by
  let K := (h.2.choose m i j q).congr (fun z hz =>
    mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
      (h.1 z hz m trivial).1 (h₀.1 m).1 i j q.property)
  exact (smoothDirections_D_sub_constant J K hk hz v).symm

/-- Full-family estimates: the reference enters only at order zero.
The loss is selected before the spatial order. This form is the input
for the fixed-base interpolation and scalar reciprocal calculations. -/
theorem CurrentJetDataOn.sourceColumns_fullTower
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
            oneHighVariationWeight (parameterGrading S) base (s + loss) z v := by
  intro k
  by_cases hk : k = 0
  · subst k
    have hheight := material_sample_height_coefficient_power_bounded hD hT cell 0
      (by norm_num : (0 : ℝ) < 3 / 4)
    let CH : ℝ := hheight.choose
    have hCH : 0 < CH := hheight.choose_spec.1
    have hheight' (m : ℕ) : T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ CH := by
      simpa only [CH, Real.rpow_zero, mul_one] using hheight.choose_spec.2 m
    have hv := h.2.choose_spec.1
    refine ⟨hv.choose, fun s => ?_⟩
    have hd := hv.choose_spec s
    have hr := h₀.2 s
    have hc := n04Realization_referenceAndDifferenceEnvelope hr.choose_spec.1.le
      hd.choose_spec.1.le hCH.le
    refine ⟨hc.choose, hc.choose_spec.1, ?_⟩
    intro m q hq i j hij J z hz v
    rw [smoothDirections_D_zero_apply J hz v]
    have he : mixedDerivative i j (f z m) q =
        mixedDerivative i j (fun y => f z m y - f₀ m y) q +
          mixedDerivative i j (f₀ m) q := by
      rw [mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (h.1 z hz m trivial).1 (h₀.1 m).1 i j hq]
      exact (sub_add_cancel _ _).symm
    rw [he]
    have hb := hc.choose_spec.2 (T.E0 (T.sample (cell m)))
      (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
      (parameterGrading S (s + hv.choose) z) _ _ (hE m) (hheight' m) (apply_nonneg _ _)
      (hr.choose_spec.2 m q hq i j hij)
      (hd.choose_spec.2 z hz m trivial ⟨q, hq⟩ i j hij)
    simpa only [parameterHeightWeight, if_pos rfl, mul_one, oneHighVariationWeight,
      Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, add_zero] using hb
  · have ht := h.2.choose_spec.2 k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro m q hq i j hij J z hz v
    rw [h.sourceColumns_positive_jet_eq h₀ m i j ⟨q, hq⟩ J
      (Nat.pos_of_ne_zero hk) hz v]
    simpa only [parameterHeightWeight, if_neg hk] using
      (ht.choose_spec s).choose_spec.2 z hz v m trivial ⟨q, hq⟩ i j hij

end Bridges

end ContinuousFlexibility.Analysis
