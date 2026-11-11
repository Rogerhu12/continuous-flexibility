import ContinuousFlexibility.Analysis.N07aLinearPhysicalBounds
import ContinuousFlexibility.Analysis.N07aMaterialInverseIntegrability
import ContinuousFlexibility.Scalar.WeightedJetNorm

/-!
# Fixed-loss bounds in the original physical norm

The pointwise majorant is an actual square-integrable function for the
supplied material coordinate. Its L² norm and the finite physical jet sum
give the original norm, without introducing a replacement grading.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators ENNReal

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base geometryLoss : ℕ} {ε γ : ℝ}
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {low loss : ℕ} {f : E → F → PolarPoint → ℝ}

theorem n07a_sampleLinearJets_weighted_memLp_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base geometryLoss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hp : Monotone p) (hq : Monotone q)
    (hf : N07aSampleLinearJetBounds T K p q U (physicalPieceOpen S K)
      (fun c m => T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      low loss (fun z u _ => f z u))
    (hfs : ∀ z ∈ U, ∀ u, ContDiffOn ℝ ∞ (f z u) (annularOpen D))
    (a b c : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z ∈ U, ∀ u,
      MemLp (weightedPhysicalJet T γ a b c (f z u)) 2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T γ a b c (f z u)) 2 materialCylinderMeasure).toReal ≤
        A * (q (a + b + c + (loss + 2)) u +
          (1 + p (a + b + c + (loss + 2)) z) * q low u) := by
  obtain ⟨A, hA, hAb⟩ := n07a_sampleLinearJets_weighted_physical_bound
    hD hT h04 href hγ hγ1 hp hq hf hfs a b c
  let R : PolarPoint → ℝ := fun x => (T.M (T.radius x.1))⁻¹
  have hR : MemLp R 2 materialCylinderMeasure := n07a_materialM_inv_cylinder_memLp hT
  let W := hR.toLp R
  have hR0 (x : PolarPoint) : 0 ≤ R x :=
    inv_nonneg.mpr (zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x.1).1).2.2.2)
  refine ⟨A * ‖W‖ + 1, by positivity, fun z hz u => ?_⟩
  let B := q (a + b + c + (loss + 2)) u +
    (1 + p (a + b + c + (loss + 2)) z) * q low u
  have hB : 0 ≤ B := add_nonneg (apply_nonneg _ _)
    (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))
  let g := weightedPhysicalJet T γ a b c (f z u)
  have hg : MemLp g 2 materialCylinderMeasure := by
    apply (hR.const_mul (A * B)).mono'
      (contDiff_weightedPhysicalJet hT (hfs z hz u) a b c).continuous.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using hAb z hz u x
  refine ⟨hg, ?_⟩
  have hn : ‖hg.toLp g‖ ≤ ‖(A * B) • W‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hg.coeFn_toLp, Lp.coeFn_smul (A * B) W, hR.coeFn_toLp]
      with x hx hxsm hxR
    rw [hx, hxsm, Pi.smul_apply, smul_eq_mul, hxR, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hA.le hB),
      abs_of_nonneg (hR0 x)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hAb z hz u x
  rw [Lp.norm_toLp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hA.le hB)] at hn
  exact hn.trans (by nlinarith only [hB])

theorem n07a_sampleLinearJets_physicalNorm_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base geometryLoss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hp : Monotone p) (hq : Monotone q)
    (hf : N07aSampleLinearJetBounds T K p q U (physicalPieceOpen S K)
      (fun c m => T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      low loss (fun z u _ => f z u))
    (hfs : ∀ z ∈ U, ∀ u, ContDiffOn ℝ ∞ (f z u) (annularOpen D))
    (s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z ∈ U, ∀ u,
      physicalNorm T γ s (f z u) ≤ A *
        (q (s + (loss + 2)) u + (1 + p (s + (loss + 2)) z) * q low u) := by
  classical
  let I := Fin (s + 1) × Fin (s + 1) × Fin (s + 1)
  choose A hA hAb using fun j : I => n07a_sampleLinearJets_weighted_memLp_bound
    hD hT h04 href hγ hγ1 hp hq hf hfs j.1.val j.2.1.val j.2.2.val
  let C₀ : ℝ := ∑ j : I, A j
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun j _ => (hA j).le)
  let Q := Real.sqrt (Fintype.card (JetIndex s) : ℝ)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  refine ⟨Q * C₀ + 1, by positivity, fun z hz u => ?_⟩
  let B := q (s + (loss + 2)) u + (1 + p (s + (loss + 2)) z) * q low u
  have hB : 0 ≤ B := add_nonneg (apply_nonneg _ _)
    (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))
  have hj (a b c : ℕ) (habc : a + b + c ≤ s) :
      MemLp (weightedPhysicalJet T γ a b c (f z u)) 2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T γ a b c (f z u)) 2 materialCylinderMeasure).toReal ≤
        C₀ * B := by
    let i : I := (⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩)
    have hi := hAb i z hz u
    refine ⟨hi.1, hi.2.trans ?_⟩
    have horder : a + b + c + (loss + 2) ≤ s + (loss + 2) :=
      Nat.add_le_add_right habc _
    have hterm : q (a + b + c + (loss + 2)) u +
        (1 + p (a + b + c + (loss + 2)) z) * q low u ≤ B :=
      add_le_add (hq horder u)
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl (hp horder z)) (apply_nonneg _ _))
    exact (mul_le_mul_of_nonneg_left hterm (hA i).le).trans
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_univ i)) hB)
  have hnorm := physicalNorm_le_of_weightedJet_bounds (mul_nonneg hC₀ hB)
    (fun a b c h => (hj a b c h).1) (fun a b c h => (hj a b c h).2)
  exact hnorm.trans (by dsimp only [Q]; nlinarith only [hB])

end ContinuousFlexibility.Analysis
