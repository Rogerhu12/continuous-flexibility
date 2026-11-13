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
  obtain ⟨rawBase, hraw⟩ := hphysical
  obtain ⟨L, hL, hheight⟩ := n04PulledFields_sampleHeight_bounded G
  refine ⟨rawBase, fun k => ?_⟩
  obtain ⟨loss, hloss⟩ := hraw k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨C, Q, hC, hQ, hbound⟩ := hloss s
  obtain ⟨B, hB, htransfer⟩ := n04PulledFields_sampledCoefficient_heightCost G hadm hC hQ
  cases k with
  | zero =>
      obtain ⟨Cref, hCref, hreference⟩ := href s
      obtain ⟨B', hB', hpack⟩ := n04PulledFields_referencePlusHeightCost
        (L := L) hCref hB.le hB.le
      refine ⟨B', hB', fun i m z hz hzlow q hq hp a b hab v => ?_⟩
      let p := G.pulledPoint η (G.lift η z) m q
      let W := oneHighVariationWeight (parameterGrading (G.S η)) rawBase (s + loss) z v
      have hW : 1 ≤ W := by
        simp only [W, oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
          mul_one, add_zero]
        exact le_add_of_nonneg_right (apply_nonneg _ _)
      have hdelta :
          |((RF i).parameter a b p hp).D 0 z v -
            mixedDerivative a b (F i (G.lift η 0)) p| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
            G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) * W := by
        have hb := hbound i z hz hzlow p hp a b hab v
        simp only [if_pos rfl] at hb
        exact hb.trans (mul_le_mul_of_nonneg_right (htransfer η z hz m q hq)
          (zero_le_one.trans hW))
      have hrestore : |((RF i).parameter a b p hp).D 0 z v| ≤
          Cref + B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
            G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) * W := by
        calc
          _ = |(((RF i).parameter a b p hp).D 0 z v -
              mixedDerivative a b (F i (G.lift η 0)) p) +
              mixedDerivative a b (F i (G.lift η 0)) p| :=
            congrArg abs (sub_add_cancel _ _).symm
          _ ≤ _ := (abs_add_le _ _).trans
            ((add_le_add hdelta (hreference i a b hab p hp)).trans_eq (add_comm _ _))
      have hfinal := hrestore.trans (hpack
        (G.W.U.E0 (G.W.U.sample ((G.V η).cell m)))
        (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) W
        ((G.cost_nonneg η).2.2 m)
        (Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _)
        (hheight η m) hW)
      simpa only [parameterHeightWeight, if_pos rfl, mul_one, p, W] using hfinal
  | succ k =>
      refine ⟨B, hB, fun i m z hz hzlow q hq hp a b hab v => ?_⟩
      have hb := hbound i z hz hzlow (G.pulledPoint η (G.lift η z) m q) hp a b hab v
      simp only [Nat.succ_ne_zero, if_false, sub_zero] at hb
      have hfinal := hb.trans (mul_le_mul_of_nonneg_right (htransfer η z hz m q hq)
        (oneHighVariationWeight_nonneg _ _ _ _ _))
      simpa only [parameterHeightWeight, Nat.succ_ne_zero, if_false] using hfinal

end ContinuousFlexibility.Analysis
