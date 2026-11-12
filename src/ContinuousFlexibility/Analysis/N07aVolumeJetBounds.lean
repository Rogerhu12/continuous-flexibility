import ContinuousFlexibility.Analysis.N07aReferenceFiniteJets
import ContinuousFlexibility.Analysis.N07aCanonicalSmoothJets

/-!
# Bounds for the actual volume jets and their smooth representatives

The same weighted jet array supplies both the genuine weak derivative
and its norm bound. The smooth decoder's actual derivative represents
that class, so no independent choice of a high-order jet is made.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aVolumeJetBoundsLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _

local instance n07aVolumeJetBoundsLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem n07aVolumeAngularJet_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {γ t : ℝ} {s : ℕ} (W : V.level γ t s) (m : ℕ) (j : Fin (s + 1)) :
    ‖n07aVolumeAngularJet (T := T) W m j‖ ≤ n07aVolumeWeight T K γ t m * ‖W‖ := by
  have hw : 0 ≤ n07aVolumeWeight T K γ t m :=
    (n07aVolumeWeight_pos (K := K) hD hT γ t m).le
  rw [n07aVolumeAngularJet, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  apply mul_le_mul_of_nonneg_left _ hw
  exact (PiLp.norm_apply_le (W.val m) j).trans
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) W.val m)

theorem n07aVolumeAngularJet_nat_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {γ : ℝ} {c s : ℕ} (W : V.level γ (c : ℝ) s) (m : ℕ) (j : Fin (s + 1)) :
    ‖n07aVolumeAngularJet (T := T) W m j‖ ≤
      (T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ c)⁻¹) * ‖W‖ := by
  have hm : 0 < T.M (T.sample (K.cell m)) := zero_lt_one.trans_le
    (hT.2.1 _ (spaces_trace_sample_mem hD hT (K.cell m))).2.2.2
  have h := n07aVolumeAngularJet_norm_le hD hT W m j
  simpa only [n07aVolumeWeight, Real.rpow_neg hm.le, Real.rpow_natCast, mul_comm] using h

theorem n07aCanonicalSmoothDecode_mixed_eLpNorm
    {m : ℕ} (hm : K.left m < K.right m) (a b : ℕ)
    (u : n07aCanonicalSmoothSpace S K m) (v : CanonicalL2 S K m)
    (hv : N07aWeakCanonicalMixedDerivative S K m u.val v a b) :
    eLpNorm (mixedDerivative a b (n07aCanonicalSmoothDecode hm u)) 2
      (canonicalMeasure S K m) = ENNReal.ofReal ‖v‖ := by
  rw [eLpNorm_congr_ae (n07aCanonicalSmoothDecode_mixed_ae hm a b u v hv),
    Lp.norm_def]
  exact (ENNReal.ofReal_toReal (Lp.memLp v).eLpNorm_ne_top).symm

theorem n07aCanonicalSmoothDecode_volume_jet_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    {γ : ℝ} {c s m : ℕ} (hm : K.left m < K.right m)
    (u : n07aCanonicalSmoothSpace S K m) (W : V.level γ (c : ℝ) s)
    (hW : V.forget γ (c : ℝ) s W m = u.val) (j : Fin (s + 1)) :
    eLpNorm (mixedDerivative 0 j.val (n07aCanonicalSmoothDecode hm u)) 2
      (canonicalMeasure S K m) ≤ ENNReal.ofReal
        ((T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ c)⁻¹) * ‖W‖) := by
  have hj := n07aVolumeAngularJet_weak hV W m j
  rw [hW] at hj
  rw [n07aCanonicalSmoothDecode_mixed_eLpNorm hm 0 j.val u _ hj]
  exact ENNReal.ofReal_le_ofReal (n07aVolumeAngularJet_nat_norm_le hD hT W m j)

end ContinuousFlexibility.Analysis
