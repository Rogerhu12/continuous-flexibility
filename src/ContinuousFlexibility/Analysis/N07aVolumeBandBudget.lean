import ContinuousFlexibility.Analysis.N07aAngularBandNorm
import ContinuousFlexibility.Analysis.N07aVolumeCell

/-!
# The physical band norm inside an actual weighted source jet

These identities use the prescribed volume graph, including all of its
weak derivatives.  They convert its outer Hilbert norm into the exact
local band quantities appearing in the mode estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aVolumeBandBudgetLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aVolumeBandBudgetLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem n07aVolume_band_piece_norm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ)
    (hI : ∀ m, K.left m < K.right m) (s n : ℕ) (W : V.level γ t s) (m : ℕ) :
    Real.sqrt (n07aAngularJetWeightSq s n) *
        ‖n07aAngularBand m (hI m) n (V.forget γ t s W m)‖ =
      n07aVolumeWeight T K γ t m * ‖(n07aAngularLevelBand hV γ t hI s n W).val m‖ := by
  have he : ‖(n07aAngularLevelBand hV γ t hI s n W).val m‖ =
      Real.sqrt (n07aAngularJetWeightSq s n) * ‖n07aAngularBand m (hI m) n (W.val m 0)‖ := by
    rw [← n07aAngularLevelLift_self hV γ t hI s n W,
      n07aAngularLevelLift_val, n07aAngularJetsLift_piece, n07aAngularBandPieceLift_norm]
  rw [he, n07aVolume_forget_apply hV, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (n07aVolumeWeight_pos hD hT γ t m)]
  ring

theorem n07aAngularLevelBand_piece_norm_le
    (hV : IsVolumeModel T S K V) (γ t : ℝ)
    (hI : ∀ m, K.left m < K.right m) (s n : ℕ) (W : V.level γ t s) (m : ℕ) :
    ‖(n07aAngularLevelBand hV γ t hI s n W).val m‖ ≤ ‖W.val m‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro k _
  rw [n07aAngularLevelBand_apply]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (n07aAngularBand_norm_le m (hI m) n (W.val m k))

theorem n07aVolume_band_piece_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ)
    (hI : ∀ m, K.left m < K.right m) (s n : ℕ) (W : V.level γ t s) (m : ℕ) :
    Real.sqrt (n07aAngularJetWeightSq s n) *
        ‖n07aAngularBand m (hI m) n (V.forget γ t s W m)‖ ≤
      n07aVolumeWeight T K γ t m * ‖W.val m‖ := by
  rw [n07aVolume_band_piece_norm hD hT hV γ t hI s n W m]
  exact mul_le_mul_of_nonneg_left
    (n07aAngularLevelBand_piece_norm_le hV γ t hI s n W m)
    (n07aVolumeWeight_pos hD hT γ t m).le

end ContinuousFlexibility.Analysis
