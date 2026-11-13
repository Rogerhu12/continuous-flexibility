import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalOneHighCurrent
import ContinuousFlexibility.Analysis.N04PulledFieldsSampledCoefficientCost

/-!
# Restoring the reference after physical-to-sample transfer

Every derivative of the physical reference difference keeps its physical
height weight. The transfer is made with that weight still present.
Only then is the uniform reference term restored at parameter order zero.
This yields the exact raw certificate used by moving-point composition.
-/

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

/-- The physical coefficient difference has one common low order. At
positive parameter order its jet is the raw jet; at zero the actual
reference spatial jet is subtracted at the same fixed physical point. -/
def N04PulledFieldsPhysicalDifferenceOneHigh {ι : Type*}
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (base : ℕ) (ε : ℝ)
    (F : ι → AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    (RF : ∀ i, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => F i (G.lift η z))) : Prop :=
  ∃ rawBase : ℕ, ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ C Q : ℝ,
    0 ≤ C ∧ 0 ≤ Q ∧ ∀ i z, z ∈ sectorNeighborhood (G.S η) base ε ε →
      parameterGrading (G.S η) rawBase z ≤ 1 →
      ∀ p (hp : p ∈ annularOpen G.W.D), ∀ a b : ℕ, a + b ≤ s →
      ∀ v : Fin k → Parameter (G.S η),
        |((RF i).parameter a b p hp).D k z v -
          (if k = 0 then mixedDerivative a b (F i (G.lift η 0)) p else 0)| ≤
          C * G.W.U.E0 p.1 ^ Q * G.W.U.H p.1 ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading (G.S η)) rawBase (s + loss) z v

private theorem n04PulledFields_oneHigh_zero_lower
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high k : ℕ) (x : E) (v : Fin k → E)
    (hk : k = 0) : 1 ≤ oneHighVariationWeight p base high x v := by
  subst k
  simp only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
    mul_one, add_zero]
  exact le_add_of_nonneg_right (apply_nonneg _ _)

/-- Restore the scalar reference before specializing the state model.
The output coefficient is uniform over all values and sampled costs. -/
private theorem n04PulledFields_restoreSampledReferenceCost
    (k : ℕ) {Cref B L : ℝ} (hCref : 0 ≤ Cref) (hB : 0 < B) :
    ∃ B' : ℝ, 0 < B' ∧ ∀ value reference E H W : ℝ,
      1 ≤ E → 0 ≤ H → H ≤ L → 0 ≤ W → (k = 0 → 1 ≤ W) →
      |reference| ≤ Cref →
      |value - (if k = 0 then reference else 0)| ≤ B * E ^ B * H * W →
      |value| ≤ B' * E ^ B' * parameterHeightWeight H k * W := by
  cases k with
  | zero =>
      obtain ⟨B', hB', hpack⟩ := n04PulledFields_referencePlusHeightCost
        (L := L) hCref hB.le hB.le
      refine ⟨B', hB', fun value reference E H W hE hH hHL _ hW href hdelta => ?_⟩
      have hrestore : |value| ≤ Cref + B * E ^ B * H * W := by
        have hb : |value - reference| ≤ B * E ^ B * H * W := by
          simpa only [if_pos rfl, ite_true] using hdelta
        calc
          _ = |(value - reference) + reference| := congrArg abs (sub_add_cancel _ _).symm
          _ ≤ _ := (abs_add_le _ _).trans
            ((add_le_add hb href).trans_eq (add_comm _ _))
      simpa only [parameterHeightWeight, if_pos rfl, ite_true, mul_one] using
        hrestore.trans (hpack E H W hE hH hHL (hW rfl))
  | succ k =>
      refine ⟨B, hB, fun value reference E H W _ _ _ _ _ _ hdelta => ?_⟩
      simpa only [parameterHeightWeight, Nat.succ_ne_zero, if_false, sub_zero] using hdelta

/-- A physical difference estimate and a uniform actual-reference
estimate give the sampled raw physical certificate on the same domain. -/
theorem n04PulledFields_sampledOneHigh_of_physicalDifference {ι : Type*}
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (F : ι → AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    (RF : ∀ i, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => F i (G.lift η z)))
    (hphysical : N04PulledFieldsPhysicalDifferenceOneHigh G η base ε F RF)
    (href : ∀ s : ℕ, ∃ Cref : ℝ, 0 ≤ Cref ∧ ∀ i a b, a + b ≤ s →
      ∀ p ∈ annularOpen G.W.D,
        |mixedDerivative a b (F i (G.lift η 0)) p| ≤ Cref) :
    N04PulledFieldsSampledPhysicalOneHigh G η base ε F RF := by
  let heightData := n04PulledFields_sampleHeight_bounded G
  refine ⟨hphysical.choose, fun k => ?_⟩
  let rawData := hphysical.choose_spec k
  refine ⟨rawData.choose, fun s => ?_⟩
  let boundData := rawData.choose_spec s
  let transfer := n04PulledFields_sampledCoefficient_heightCost G hadm
    boundData.choose_spec.choose_spec.1 boundData.choose_spec.choose_spec.2.1
  let referenceData := href s
  let restored := n04PulledFields_restoreSampledReferenceCost k
    (L := heightData.choose) referenceData.choose_spec.1 transfer.choose_spec.1
  refine ⟨restored.choose, restored.choose_spec.1,
    fun i m z hz hzlow q hq hp a b hab v => ?_⟩
  let p := G.pulledPoint η (G.lift η z) m q
  let W := oneHighVariationWeight (parameterGrading (G.S η))
    hphysical.choose (s + rawData.choose) z v
  have hW : 0 ≤ W := oneHighVariationWeight_nonneg _ _ _ _ _
  apply restored.choose_spec.2
    (((RF i).parameter a b p hp).D k z v)
    (mixedDerivative a b (F i (G.lift η 0)) p)
    (G.W.U.E0 (G.W.U.sample ((G.V η).cell m)))
    (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) W
    ((G.cost_nonneg η).2.2 m)
    (Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _)
    (heightData.choose_spec.2 η m) hW
    (n04PulledFields_oneHigh_zero_lower _ _ _ _ _ _)
    (referenceData.choose_spec.2 i a b hab p hp)
  exact (boundData.choose_spec.choose_spec.2.2 i z hz hzlow p hp a b hab v).trans
    (mul_le_mul_of_nonneg_right (transfer.choose_spec.2 η z hz m q hq) hW)

end ContinuousFlexibility.Analysis
