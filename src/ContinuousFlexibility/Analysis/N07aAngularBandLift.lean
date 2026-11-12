import ContinuousFlexibility.Analysis.N07aAngularJetBands
import ContinuousFlexibility.Analysis.N07aAngularBandDerivative

/-!
# Actual higher-level realization of one angular band

All higher derivatives are constructed by the bounded band multipliers
on the original real canonical pieces. The construction is square
summable over every radial component and belongs to the frozen volume
graph. Truncating it returns the original projected source.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S}

def n07aAngularBandPieceLift (m : ℕ) (hm : K.left m < K.right m) (t n : ℕ)
    (u : CanonicalL2 S K m) : PiLp 2 (fun _ : Fin (t + 1) => CanonicalL2 S K m) :=
  WithLp.toLp 2 (fun k => n07aAngularBandDerivative m hm n k.val u)

@[simp] theorem n07aAngularBandPieceLift_apply (m : ℕ) (hm : K.left m < K.right m)
    (t n : ℕ) (u : CanonicalL2 S K m) (k : Fin (t + 1)) :
    n07aAngularBandPieceLift m hm t n u k = n07aAngularBandDerivative m hm n k.val u := by
  simp only [n07aAngularBandPieceLift, PiLp.toLp_apply]

theorem n07aAngularBandPieceLift_norm_sq (m : ℕ) (hm : K.left m < K.right m)
    (t n : ℕ) (u : CanonicalL2 S K m) :
    ‖n07aAngularBandPieceLift m hm t n u‖ ^ 2 =
      n07aAngularJetWeightSq t n * ‖n07aAngularBand m hm n u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ k : Fin (t + 1), ‖n07aAngularBandPieceLift m hm t n u k‖ ^ 2) =
        ∑ k : Fin (t + 1), n07aAngularFrequencySquare n ^ k.val *
          ‖n07aAngularBand m hm n u‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [n07aAngularBandPieceLift_apply, n07aAngularBandDerivative_norm, mul_pow]
      congr 1
      rw [n07aAngularFrequencySquare, ← pow_mul, ← pow_mul, Nat.mul_comm k.val 2]
    _ = (∑ k : Fin (t + 1), n07aAngularFrequencySquare n ^ k.val) *
        ‖n07aAngularBand m hm n u‖ ^ 2 := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [Fin.sum_univ_eq_sum_range]; rfl

theorem n07aAngularBandPieceLift_norm (m : ℕ) (hm : K.left m < K.right m)
    (t n : ℕ) (u : CanonicalL2 S K m) :
    ‖n07aAngularBandPieceLift m hm t n u‖ =
      Real.sqrt (n07aAngularJetWeightSq t n) * ‖n07aAngularBand m hm n u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [n07aAngularBandPieceLift_norm_sq, mul_pow,
    Real.sq_sqrt (n07aAngularJetWeightSq_nonneg t n)]

theorem n07aAngularBandPieceLift_norm_le (m : ℕ) (hm : K.left m < K.right m)
    (t n : ℕ) (u : CanonicalL2 S K m) :
    ‖n07aAngularBandPieceLift m hm t n u‖ ≤ Real.sqrt (n07aAngularJetWeightSq t n) * ‖u‖ := by
  rw [n07aAngularBandPieceLift_norm]
  exact mul_le_mul_of_nonneg_left (n07aAngularBand_norm_le m hm n u) (Real.sqrt_nonneg _)

def n07aAngularJetsLift (hK : ∀ m, K.left m < K.right m) (b t n : ℕ)
    (u : CanonicalVolumeJets S K b) : CanonicalVolumeJets S K t :=
  ⟨fun m => n07aAngularBandPieceLift m (hK m) t n (u m 0),
    (lp.memℓp (Real.sqrt (n07aAngularJetWeightSq t n) • u)).mono' (fun m => by
      rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (n07aAngularBandPieceLift_norm_le m (hK m) t n _).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (u m) 0) (Real.sqrt_nonneg _)))⟩

@[simp] theorem n07aAngularJetsLift_piece (hK : ∀ m, K.left m < K.right m) (b t n : ℕ)
    (u : CanonicalVolumeJets S K b) (m : ℕ) :
    n07aAngularJetsLift hK b t n u m = n07aAngularBandPieceLift m (hK m) t n (u m 0) := rfl

@[simp] theorem n07aAngularJetsLift_apply (hK : ∀ m, K.left m < K.right m) (b t n : ℕ)
    (u : CanonicalVolumeJets S K b) (m : ℕ) (k : Fin (t + 1)) :
    n07aAngularJetsLift hK b t n u m k = n07aAngularBandDerivative m (hK m) n k.val (u m 0) :=
  n07aAngularBandPieceLift_apply m (hK m) t n (u m 0) k

theorem n07aAngularJetsLift_mem_graph (hK : ∀ m, K.left m < K.right m) (b t n : ℕ)
    {u : CanonicalVolumeJets S K b} (hu : u ∈ canonicalVolumeGraph S K b) :
    n07aAngularJetsLift hK b t n u ∈ canonicalVolumeGraph S K t := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa only [n07aAngularJetsLift_apply, Fin.val_zero, n07aAngularBandDerivative_zero] using
      n07aAngularBand_even m (hK m) n (hu.1 m)
  · intro m k
    simpa only [n07aAngularJetsLift_apply, Fin.val_zero, n07aAngularBandDerivative_zero] using
      n07aAngularBandDerivative_weak m (hK m) n k.val (u m 0)

variable {T : MaterialData} {V : VolumeModelData S K}

def n07aAngularLevelLift (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b t n : ℕ) (u : V.level γ w b) : V.level γ w t :=
  ⟨n07aAngularJetsLift hK b t n u.val, by
    have hu : u.val ∈ canonicalVolumeGraph S K b := by
      rw [← hV.1 γ w b]
      exact u.property
    have h := n07aAngularJetsLift_mem_graph hK b t n hu
    rwa [← hV.1 γ w t] at h⟩

@[simp] theorem n07aAngularLevelLift_val (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b t n : ℕ) (u : V.level γ w b) :
    (n07aAngularLevelLift hV γ w hK b t n u).val = n07aAngularJetsLift hK b t n u.val := rfl

@[simp] theorem n07aAngularLevelLift_apply (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b t n : ℕ) (u : V.level γ w b)
    (m : ℕ) (k : Fin (t + 1)) :
    (n07aAngularLevelLift hV γ w hK b t n u).val m k =
      n07aAngularBandDerivative m (hK m) n k.val (u.val m 0) := by
  rw [n07aAngularLevelLift_val, n07aAngularJetsLift_apply]

theorem n07aAngularLevelLift_band (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (b t n : ℕ) (u : V.level γ w b) :
    n07aAngularLevelBand hV γ w hK t n (n07aAngularLevelLift hV γ w hK b t n u) =
      n07aAngularLevelLift hV γ w hK b t n u := by
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro k
  rw [n07aAngularLevelBand_apply, n07aAngularLevelLift_apply, n07aAngularBandDerivative_band]

theorem n07aAngularLevelLift_truncate (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) {b t : ℕ} (hbt : b ≤ t) (n : ℕ)
    (u : V.level γ w b) :
    n07aAngularLevelTruncate hV γ w hbt (n07aAngularLevelLift hV γ w hK b t n u) =
      n07aAngularLevelBand hV γ w hK b n u := by
  have hu : u.val ∈ canonicalVolumeGraph S K b := by
    rw [← hV.1 γ w b]
    exact u.property
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro k
  rw [n07aAngularLevelTruncate_apply, n07aAngularLevelLift_apply,
    n07aAngularOrderEmbedding_val, n07aAngularLevelBand_apply]
  exact n07aAngularBandDerivative_eq_of_weak m (hK m) n (hu.2 m k)

theorem n07aAngularLevelLift_of_truncate (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) {b t : ℕ} (hbt : b ≤ t) (n : ℕ)
    (u : V.level γ w t) :
    n07aAngularLevelLift hV γ w hK b t n (n07aAngularLevelTruncate hV γ w hbt u) =
      n07aAngularLevelBand hV γ w hK t n u := by
  have hu : u.val ∈ canonicalVolumeGraph S K t := by
    rw [← hV.1 γ w t]
    exact u.property
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro k
  rw [n07aAngularLevelLift_apply, n07aAngularLevelTruncate_apply,
    n07aAngularOrderEmbedding_zero, n07aAngularLevelBand_apply]
  exact n07aAngularBandDerivative_eq_of_weak m (hK m) n (hu.2 m k)

theorem n07aAngularLevelTruncate_band (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) {b t : ℕ} (hbt : b ≤ t) (n : ℕ)
    (u : V.level γ w t) :
    n07aAngularLevelTruncate hV γ w hbt (n07aAngularLevelBand hV γ w hK t n u) =
      n07aAngularLevelBand hV γ w hK b n (n07aAngularLevelTruncate hV γ w hbt u) := by
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro k
  rw [n07aAngularLevelTruncate_apply, n07aAngularLevelBand_apply,
    n07aAngularLevelBand_apply, n07aAngularLevelTruncate_apply]

end ContinuousFlexibility.Statements
