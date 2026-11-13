import ContinuousFlexibility.Analysis.N04PulledFieldsInverseJoint
import ContinuousFlexibility.Analysis.CanonicalStripGeometry

/-!
# Spatial regularity of the actual pulled fields

Admissibility gives the same inverse chart and its physical range.  Its
spatial smoothness and angular equivariance transport the actual physical
fields to the unit strip.  These qualitative conclusions require no
quantitative reference-jet certificate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

theorem n04PulledFields_unitPoint_mapsTo
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) (m : ℕ) :
    MapsTo (canonicalUnitPoint (G.V η) m) unitStrip
      (canonicalOpen (G.S η) (G.V η) m) := by
  have hlen := ((n04PulledFields_admissible_geometry G η hadm).referenceBounds m).2.1
  intro y hy
  have hl := mul_pos (sub_pos.mpr hlen) hy.1.1
  have hu := mul_lt_of_lt_one_right (sub_pos.mpr hlen) hy.1.2
  refine ⟨?_, mem_univ _⟩
  dsimp only [canonicalUnitPoint]
  constructor <;> linarith

/-- The genuine inverse point is smooth in both spatial coordinates. -/
theorem n04PulledFields_pulledPoint_spatial
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) base ε ε) (m : ℕ) :
    ContDiffOn ℝ ∞ (G.pulledPoint η (G.lift η z) m) unitStrip := by
  have hg := n04PulledFields_admissible_geometry G η hadm
  have hzstate := liftSectorParameter_mem_stateNeighborhood (C := G.C η) hz le_rfl
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hu : ContDiff ℝ ∞ (canonicalUnitPoint (G.V η) m) := by
    unfold canonicalUnitPoint
    fun_prop
  exact (hg.charts _ hzstate hs m).2.2.2.2.2.1.comp hu.contDiffOn
    (n04PulledFields_unitPoint_mapsTo G η hadm m)

/-- Angular equivariance uses the actual inverse identities and physical
domain invariance; it is retained at the canonical unit point. -/
theorem n04PulledFields_pulledPoint_periodic
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) base ε ε)
    (m : ℕ) {y : PolarPoint} (hy : y ∈ unitStrip) :
    G.pulledPoint η (G.lift η z) m (y + (0, Real.pi)) =
      G.pulledPoint η (G.lift η z) m y + (0, Real.pi) := by
  have hg := n04PulledFields_admissible_geometry G η hadm
  have hzstate := liftSectorParameter_mem_stateNeighborhood (C := G.C η) hz le_rfl
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have h := canonicalInverse_periodic_on_open hg hzstate hs m
    (n04PulledFields_unitPoint_mapsTo G η hadm m hy)
  simpa only [N04RealizationGauge.pulledPoint, canonicalUnitPoint,
    Prod.fst_add, Prod.snd_add, add_zero, Prod.mk_add_mk] using h

/-- The full spatial clause of `CurrentJetDataOn` follows from actual
physical regularity, without an estimate for any composed field. -/
theorem n04PulledFields_spatial_of_physical
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) base ε ε)
    (hsmooth : ContDiffOn ℝ ∞ (F (G.lift η z)) (annularOpen G.W.D))
    (hperiodic : ∀ p ∈ annularOpen G.W.D,
      F (G.lift η z) (p + (0, Real.pi)) = F (G.lift η z) p) (m : ℕ) :
    ContDiffOn ℝ ∞ (G.pulled η F z m) unitStrip ∧
      ∀ y ∈ unitStrip, G.pulled η F z m (y + (0, Real.pi)) = G.pulled η F z m y := by
  have hproduct := n04PulledFields_pulledPoint_mapsTo G η hadm m
  have hmap : MapsTo (G.pulledPoint η (G.lift η z) m) unitStrip (annularOpen G.W.D) :=
    fun y hy => @hproduct (z, y) ⟨hz, hy⟩
  refine ⟨hsmooth.comp (n04PulledFields_pulledPoint_spatial G η hadm hz m) hmap, ?_⟩
  intro y hy
  change F (G.lift η z) (G.pulledPoint η (G.lift η z) m (y + (0, Real.pi))) = _
  rw [n04PulledFields_pulledPoint_periodic G η hadm hz m hy]
  exact hperiodic _ (hmap hy)

/-- All three literal corrected coefficients satisfy the spatial clause
on the unchanged admissible neighborhood, before choosing reference jets. -/
theorem n04PulledFields_coefficient_spatial
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) base ε ε)
    (c : Fin 3) (m : ℕ) :
    ContDiffOn ℝ ∞ (G.pulled η (G.coefficientField η c) z m) unitStrip ∧
      ∀ y ∈ unitStrip,
        G.pulled η (G.coefficientField η c) z m (y + (0, Real.pi)) =
          G.pulled η (G.coefficientField η c) z m y := by
  have hzstate : G.lift η z ∈ stateNeighborhood G.W.S G.W.C G.W.base G.W.ε :=
    stateNeighborhood_mono G.W.S G.W.C hadm.1 hadm.2.2.1
      (liftSectorParameter_mem_stateNeighborhood (C := G.C η) hz le_rfl)
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hreg := G.W.field.smooth_coefficients _ hzstate hs
  apply n04PulledFields_spatial_of_physical G η hadm (G.coefficientField η c) hz
  · unfold N04RealizationGauge.coefficientField canonicalCoefficientComponent
    split_ifs
    · exact hreg.1
    · exact hreg.2.1
    · exact hreg.2.2
  · intro p hp
    have hper := G.W.field.periodic_coefficients _ hzstate hs p.1 hp.1
    have hpadd : p + (0, Real.pi) = (p.1, p.2 + Real.pi) :=
      Prod.ext (add_zero p.1) rfl
    unfold N04RealizationGauge.coefficientField canonicalCoefficientComponent
    rw [hpadd]
    split_ifs
    · exact hper.1 p.2
    · exact hper.2.1 p.2
    · exact hper.2.2 p.2

/-- The reference family in the target is the zero-parameter value of
the same pulled physical field, exactly as required by the value estimate. -/
theorem n04PulledFields_pulled_zero
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ) (m : ℕ) :
    G.pulled η F 0 m = G.pulledRef η F m := by
  have hz : G.lift η (0 : Parameter (G.S η)) = G.ref η := by
    simp only [N04RealizationGauge.lift, N04RealizationGauge.ref, liftSectorParameter,
      Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero, add_zero]
  exact congrArg (fun w : AnnularState (G.S η) × ℝ =>
    fun y => F w (G.pulledPoint η w m y)) hz

end ContinuousFlexibility.Analysis
