module

public import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalOneHighPrefix
public import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalCurrent
public import ContinuousFlexibility.Analysis.N04PulledFieldsJointExpansion

/-!
# Actual current data from sampled physical one-high estimates

The input differentiates each physical field at a fixed physical point,
then evaluates that derivative at the retained inverse chart. One raw
low order works for the whole field family. Interpolation and the
independent inverse prefix choose one smaller neighborhood before the
field index. The full current data follow on that same neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency false

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

/-- A raw physical estimate at the retained point, with the cost at the
retained sample. The parameter derivative is taken before evaluation at
the moving point. This is not an estimate for a pulled derivative. -/
def N04PulledFieldsSampledPhysicalOneHigh {ι : Type*}
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (base : ℕ) (ε : ℝ)
    (F : ι → AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    (RF : ∀ i, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => F i (G.lift η z))) : Prop :=
  ∃ rawBase : ℕ, ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ i m z, z ∈ sectorNeighborhood (G.S η) base ε ε →
    parameterGrading (G.S η) rawBase z ≤ 1 → ∀ q ∈ unitStrip,
    ∀ hp : G.pulledPoint η (G.lift η z) m q ∈ annularOpen G.W.D,
    ∀ a b : ℕ, a + b ≤ s → ∀ v : Fin k → Parameter (G.S η),
      |((RF i).parameter a b (G.pulledPoint η (G.lift η z) m q) hp).D k z v| ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
          parameterHeightWeight
            (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) k *
          oneHighVariationWeight (parameterGrading (G.S η)) rawBase (s + loss) z v

private theorem n04PulledFields_sampledPhysical_prefix {ι : Type*}
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (F : ι → AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    (RF : ∀ i, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => F i (G.lift η z)))
    (hraw : N04PulledFieldsSampledPhysicalOneHigh G η base ε F RF) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ offset : ℕ,
      ∀ top : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ i m z, z ∈ sectorNeighborhood (G.S η) base ε ε →
      parameterGrading (G.S η) low z ≤ 1 → ∀ q ∈ unitStrip,
      ∀ hp : G.pulledPoint η (G.lift η z) m q ∈ annularOpen G.W.D,
      ∀ a b j : ℕ, j ≤ K → a + b ≤ top →
      ∀ u : Fin j → Parameter (G.S η),
        (∀ d, parameterGrading (G.S η) low (u d) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
        parameterGrading (G.S η) (top + (low + offset + 1)) z ≤ R →
        (∀ d, parameterGrading (G.S η) (top + (low + offset + 1)) (u d) ≤ R) →
        |((RF i).parameter a b (G.pulledPoint η (G.lift η z) m q) hp).D j z u| ≤
          C * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
            parameterHeightWeight
              (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) j *
            (R ^ (1 / ((top : ℝ) + 1))) ^ (a + b + offset) := by
  classical
  let T : ∀ k : ℕ, (ι × ℕ × unitStrip) → ℕ → ℕ →
      Parameter (G.S η) → (Fin k → Parameter (G.S η)) → ℝ :=
    fun k t a b z v =>
      if hp : G.pulledPoint η (G.lift η z) t.2.1 t.2.2.val ∈ annularOpen G.W.D then
        ((RF t.1).parameter a b
          (G.pulledPoint η (G.lift η z) t.2.1 t.2.2.val) hp).D k z v
      else 0
  have hmap : ∀ m, MapsTo
      (fun x : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η x.1) m x.2)
      (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip) (annularOpen G.W.D) :=
    fun m => n04PulledFields_pulledPoint_mapsTo G η hadm m
  have hprefix := n04PulledFields_physicalPrefix_of_smallOneHigh T
    (parameterGrading (G.S η)) (n07aParameterGrading_monotone (G.S η))
    (n04PulledFields_parameter_hasInterpolation G η) base
    (fun t => G.W.U.E0 (G.W.U.sample ((G.V η).cell t.2.1)))
    (fun t => G.W.U.H (G.W.U.sample ((G.V η).cell t.2.1)) ^ (3 / 4 : ℝ))
    (fun t => (G.cost_nonneg η).2.2 t.2.1)
    (fun t => Real.rpow_nonneg ((G.cost_nonneg η).2.1 t.2.1) _)
    (by
      refine hraw.elim fun rawBase hraw => ⟨rawBase, fun k => ?_⟩
      refine (hraw k).elim fun loss hloss => ⟨loss, fun s => ?_⟩
      refine (hloss s).elim fun B hB => ⟨B, hB.1, ?_⟩
      intro t a b hab z hz hzsmall v
      have hp := @hmap t.2.1 (z, t.2.2.val) ⟨hz, t.2.2.property⟩
      simpa only [T, dif_pos hp] using
        hB.2 t.1 t.2.1 z hz hzsmall t.2.2.val t.2.2.property hp a b hab v)
  refine hprefix.elim fun low hlow => ⟨low, hlow.1, fun K => ?_⟩
  refine (hlow.2 K).elim fun offset hoffset => ⟨offset, fun top => ?_⟩
  refine (hoffset top).elim fun C hC => hC.elim fun A hCA => ?_
  refine ⟨C, A, hCA.1, hCA.2.1, ?_⟩
  intro i m z hz hzsmall q hq hp a b j hj hab u hu R hR hzR huR
  simpa only [T, dif_pos hp] using
    hCA.2.2 j hj a b hab (i, m, ⟨q, hq⟩) z hz hzsmall u hu R hR hzR huR

/-- One sampled raw physical certificate for the whole family gives
complete current data on one smaller neighborhood. The genuine joint
tower supplies its mixed expansion, and the inverse data are constructed
from the current geometry and the same-atlas reference certificate. -/
theorem n04PulledFields_physicalOneHigh_currentData {ι : Type*}
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hgeo : G.GeometryData η (fun _ => True) base ε) (href : G.ReferenceData η)
    (F : ι → AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    (RF : ∀ i, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => F i (G.lift η z)))
    (JF : ∀ i, SmoothDirections
      (sectorNeighborhood (G.S η) base ε ε ×ˢ annularOpen G.W.D)
      (fun x : Parameter (G.S η) × PolarPoint => F i (G.lift η x.1) x.2))
    (hperiodic : ∀ i z, z ∈ sectorNeighborhood (G.S η) base ε ε →
      ∀ p ∈ annularOpen G.W.D,
        F i (G.lift η z) (p + (0, Real.pi)) = F i (G.lift η z) p)
    (hraw : N04PulledFieldsSampledPhysicalOneHigh G η base ε F RF) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i, G.Data η (fun _ => True) base' ε' (G.pulled η (F i)) (G.pulledRef η (F i)) := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  refine (n04PulledFields_sampledPhysical_prefix G η hadm F RF hraw).elim
    fun physicalLow hphysical => ?_
  refine (n04PulledFields_inversePoint_neighborhood G η hadm hgeo href).elim
    fun inverseLow hinverse => ?_
  let base' : ℕ := max physicalLow inverseLow
  let δ : ℝ := min ε (1 / 2)
  have hphys : physicalLow ≤ base' := le_max_left _ _
  have hinv : inverseLow ≤ base' := le_max_right _ _
  have hb : base ≤ base' := hphysical.1.trans hphys
  have hδ : 0 < δ := lt_min hadm.2.1 (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hadm' : G.Admissible base' δ := G.admissible_mono hadm hb hδ hδε
  have hsub : sectorNeighborhood (G.S η) base' δ δ ⊆
      sectorNeighborhood (G.S η) base ε ε := sectorNeighborhood_mono (G.S η) hb hδε hδε
  have hU := isOpen_sectorNeighborhood (G.S η) base' δ δ
  have hV : IsOpen (annularOpen G.W.D) := isOpen_Ioo.prod isOpen_univ
  have hc : Convex ℝ (sectorNeighborhood (G.S η) base' δ δ ×ˢ annularOpen G.W.D) :=
    (sectorNeighborhood_convex (G.S η) base' δ δ).prod ((convex_Ioo _ _).prod convex_univ)
  let RF' : ∀ i, MixedJetRegularity (sectorNeighborhood (G.S η) base' δ δ)
      (annularOpen G.W.D) (fun z => F i (G.lift η z)) :=
    fun i => ⟨fun z hz => (RF i).spatial z (hsub hz),
      fun a b p hp => ((RF i).parameter a b p hp).restrict hU hsub⟩
  let JF' : ∀ i, SmoothDirections
      (sectorNeighborhood (G.S η) base' δ δ ×ˢ annularOpen G.W.D)
      (fun x : Parameter (G.S η) × PolarPoint => F i (G.lift η x.1) x.2) :=
    fun i => (JF i).restrict (hU.prod hV) (fun _ hx => ⟨hsub hx.1, hx.2⟩)
  refine (hinverse.2 base' δ hinv hδε hhalf).elim fun IP => ?_
  refine ⟨base', δ, hb, hδ, hδε, fun i => ?_⟩
  refine n04PulledFields_physical_currentData G η hadm' hhalf (F i) (RF' i) (JF' i)
    (fun n z hz p hp v =>
      n04PulledFields_jointDirections_mixedExpansion (JF' i) (RF' i) hU hV hc
        n z hz p hp v)
    (fun z hz => hperiodic i z (hsub hz)) IP ?_
  intro K
  refine (hphysical.2 K).elim fun offset hoffset =>
    ⟨offset, physicalLow + offset + 1, fun top => ?_⟩
  refine (hoffset top).elim fun C hC => hC.elim fun A hCA => ?_
  refine ⟨C, A, hCA.1, hCA.2.1, ?_⟩
  intro m z hz q hq hp a b j hj hab u hu R hR hzR huR
  have hzsmall : parameterGrading (G.S η) physicalLow z ≤ 1 :=
    (n07aParameterGrading_monotone (G.S η) hphys z).trans
      (n04PulledFields_parameterGrading_le_one (G.S η) hhalf hz)
  exact hCA.2.2 i m z (hsub hz) hzsmall q hq hp a b j hj hab u
    (fun d => (n07aParameterGrading_monotone (G.S η) hphys (u d)).trans (hu d))
    R hR hzR huR

end ContinuousFlexibility.Analysis
