import ContinuousFlexibility.Analysis.N07aCanonicalJetNormBounds
import ContinuousFlexibility.Analysis.N07aLinearJetCoefficient
import ContinuousFlexibility.Analysis.N07aSourceWeightCancellation
import ContinuousFlexibility.Analysis.N07aModeBudgetMaterial
import ContinuousFlexibility.Analysis.N07aAngularPieceSummability

/-!
# The actual source-linear jets give every prescribed volume level

All finite jet and interval factors are collected before using one
material power. The second extra material power supplies the outer lp
summability of the genuine source classes, with a fixed order loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {V : VolumeModelData S K}
  {base geometryLoss : ℕ} {ε γ : ℝ}
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {low loss : ℕ} {f : E → F → ℕ → PolarPoint → ℝ}

local instance n07aLinearJetVolumeLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) :=
  Submodule.normedAddCommGroup _

local instance n07aLinearJetVolumeLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) :=
  Submodule.normedSpace _

theorem n07a_sampleLinearJet_volume_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base geometryLoss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hV : IsVolumeModel T S K V) (hp : Monotone p) (hq : Monotone q)
    (hf : N07aSampleLinearJetBounds T K p q U (canonicalOpen S K)
      (fun c m => T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      low loss f)
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (canonicalOpen S K m))
    (hfp : ∀ z ∈ U, ∀ u m y, y ∈ canonicalOpen S K m →
      f z u m (y + (0, Real.pi)) = f z u m y)
    (hfe : ∀ z ∈ U, ∀ u m y, y ∈ canonicalOpen S K m →
      f z u m (y.1, -y.2) = f z u m y) (t s : ℕ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ z ∈ U, ∀ u : F,
      ∃ Fts : V.level γ (t : ℝ) s,
        (∀ m, (V.forget γ (t : ℝ) s Fts m : PolarPoint → ℝ)
          =ᵐ[canonicalMeasure S K m] f z u m) ∧
        ‖Fts‖ ≤ C₀ * (q (t + s + (loss + 2)) u +
          (1 + p (t + s + (loss + 2)) z) * q low u) := by
  classical
  let w := fun c m => T.H (T.sample (K.cell m)) ^ γ *
    (T.M (T.sample (K.cell m)) ^ c)⁻¹
  have hpos (m : ℕ) := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  have hw (c m : ℕ) : 0 ≤ w c m :=
    mul_nonneg (Real.rpow_pos_of_pos (hpos m).2.1 γ).le
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (hpos m).2.2.2) c))
  choose e he he0 heb using fun j : Fin (s + 1) => hf 0 j.val (t + 2)
  let env : ℕ → ℝ := fun m => Real.sqrt (Real.pi * (K.right m - K.left m)) * ∑ j, e j m
  have henv : N07aSampleSubpower T K env :=
    N07aSampleSubpower.mul hD hT (n07a_canonicalModeNormalization_subpower hD hT href)
      (N07aSampleSubpower.finset_sum hD hT Finset.univ e (fun j _ => he j))
  obtain ⟨A, hA, hAb⟩ := henv.one_power
  have henv0 (m : ℕ) : 0 ≤ env m :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun j _ => he0 j m))
  have hsum := n07a_physicalPiece_sampleInverse_summable hD hT h04 href
  have hsumm : Summable (fun m => (T.M (T.sample (K.cell m)))⁻¹) := hsum.choose_spec.2.1
  let Z := Real.sqrt (∑' m, (T.M (T.sample (K.cell m)))⁻¹)
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  refine ⟨Z * A + 1, by positivity, fun z hz u => ?_⟩
  let B := q (t + s + (loss + 2)) u + (1 + p (t + s + (loss + 2)) z) * q low u
  have hB : 0 ≤ B := add_nonneg (apply_nonneg _ _)
    (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))
  let χ : ∀ m, N07aCanonicalOpenCoefficient S K m :=
    fun m => hf.openCoefficient hw hfs hfp z hz u m
  let a : ℕ → ℝ := fun m => (n07aVolumeWeight T K γ (t : ℝ) m)⁻¹
  let v := n07aCanonicalCoefficientJetArray χ s a
  have ha (m : ℕ) : 0 ≤ a m := (inv_pos.mpr (n07aVolumeWeight_pos hD hT γ (t : ℝ) m)).le
  have hjet (m : ℕ) (j : Fin (s + 1)) :
      ‖((χ m).jet 0 j.val).toLp‖ ≤
        Real.sqrt (Real.pi * (K.right m - K.left m)) * (e j m * w (t + 2) m * B) := by
    apply ((χ m).jet 0 j.val).toLp_norm_le (h04.1.referenceBounds m).2.1
      (mul_nonneg (mul_nonneg (he0 j m) (hw _ m)) hB)
    apply (n07a_canonicalOpen_ae (S := S) (K := K) (m := m)).mono
    intro y hy
    apply (heb j z hz u m y hy).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (he0 j m) (hw _ m))
    have hj : t + 2 + (0 + j.val) + loss ≤ t + s + (loss + 2) := by
      have hj := j.isLt
      omega
    exact add_le_add (hq hj u)
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl (hp hj z)) (apply_nonneg _ _))
  have hv (m : ℕ) : ‖v m‖ ≤ A * (T.M (T.sample (K.cell m)))⁻¹ * B := by
    have hfirst : ‖v m‖ ≤ a m * env m * w (t + 2) m * B := by
      apply (n07a_piLp_two_norm_le_sum_norm (v m)).trans
      calc
        (∑ j, ‖v m j‖) ≤ ∑ j : Fin (s + 1),
            a m * (Real.sqrt (Real.pi * (K.right m - K.left m)) *
              (e j m * w (t + 2) m * B)) := by
          apply Finset.sum_le_sum
          intro j _
          rw [n07aCanonicalCoefficientJetArray_apply, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg (ha m)]
          exact mul_le_mul_of_nonneg_left (hjet m j) (ha m)
        _ = _ := by
          dsimp only [env]
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    have hcancel : a m * w (t + 2) m = (T.M (T.sample (K.cell m)) ^ 2)⁻¹ :=
      n07a_volumeWeight_inverse_nat (zero_lt_one.trans_le (hpos m).2.2.2) (hpos m).2.1 t
    calc
      ‖v m‖ ≤ env m * (a m * w (t + 2) m) * B := hfirst.trans_eq (by ring)
      _ = env m * (T.M (T.sample (K.cell m)) ^ 2)⁻¹ * B := by rw [hcancel]
      _ ≤ (A * T.M (T.sample (K.cell m))) *
          (T.M (T.sample (K.cell m)) ^ 2)⁻¹ * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          ((le_abs_self _).trans (hAb m)) (inv_nonneg.mpr (sq_nonneg _))) hB
      _ = _ := by
        field_simp [(zero_lt_one.trans_le (hpos m).2.2.2).ne'] <;> ring
  have hb (m : ℕ) : ‖v m‖ ^ 2 ≤ (T.M (T.sample (K.cell m)))⁻¹ * (A * B) ^ 2 :=
    n07a_materialInverse_square_bound (norm_nonneg _) hA.le hB (hpos m).2.2.2 (hv m)
  obtain ⟨hmem, hnorm⟩ := n07a_lp_of_square_majorant v
    (fun m => (T.M (T.sample (K.cell m)))⁻¹) hsumm
    (fun m => inv_nonneg.mpr (zero_le_one.trans (hpos m).2.2.2)) (mul_nonneg hA.le hB) hb
  let Fts := n07aOpenCoefficientVolume hV γ (t : ℝ) s χ (hfe z hz u) hmem
  refine ⟨Fts, ?_, ?_⟩
  · have hforget : V.forget γ (t : ℝ) s Fts = fun m => (χ m).toLp :=
      n07aOpenCoefficientVolume_forget hD hT hV γ (t : ℝ) s χ (hfe z hz u) hmem
    intro m
    rw [congrFun hforget m]
    exact (χ m).toLp_ae
  · change ‖(⟨v, hmem⟩ : CanonicalVolumeJets S K s)‖ ≤ _
    exact hnorm.trans (by dsimp only [Z]; nlinarith only [hB])

end ContinuousFlexibility.Analysis
