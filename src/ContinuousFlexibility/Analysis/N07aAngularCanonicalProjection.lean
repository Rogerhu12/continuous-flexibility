import ContinuousFlexibility.Analysis.N07aAngularJetBands

/-!
# Angular projection on the actual canonical fields and scalar unknowns

The componentwise band commutes with the prescribed material weight in
`VolumeModelData.forget`.  The three genuine scalar components have
frequencies `0`, `1`, `0`, respectively: the middle component multiplies
the physical `cos(2θ)` border column.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal

variable {S : PhysicalSpacesData} {K : CanonicalData S}

def n07aAngularSequenceBand (hK : ∀ m, K.left m < K.right m) (n : ℕ)
    (f : CanonicalSequence S K) : CanonicalSequence S K :=
  fun m => n07aAngularBand m (hK m) n (f m)

@[simp] theorem n07aAngularSequenceBand_apply (hK : ∀ m, K.left m < K.right m)
    (n : ℕ) (f : CanonicalSequence S K) (m : ℕ) :
    n07aAngularSequenceBand hK n f m = n07aAngularBand m (hK m) n (f m) := rfl

def n07aAngularL2SequenceBand (hK : ∀ m, K.left m < K.right m) (n : ℕ)
    (u : CanonicalL2Sequence S K) : CanonicalL2Sequence S K :=
  ⟨n07aAngularSequenceBand hK n u,
    (lp.memℓp u).mono' (fun m => n07aAngularBand_norm_le m (hK m) n (u m))⟩

@[simp] theorem n07aAngularL2SequenceBand_apply (hK : ∀ m, K.left m < K.right m)
    (n : ℕ) (u : CanonicalL2Sequence S K) (m : ℕ) :
    n07aAngularL2SequenceBand hK n u m = n07aAngularBand m (hK m) n (u m) := rfl

theorem n07aAngularL2SequenceBand_norm_le (hK : ∀ m, K.left m < K.right m)
    (n : ℕ) (u : CanonicalL2Sequence S K) : ‖n07aAngularL2SequenceBand hK n u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro m
  exact n07aAngularBand_norm_le m (hK m) n (u m)

def n07aAngularUnknownBand (hK : ∀ m, K.left m < K.right m)
    (n : ℕ) (U : CanonicalUnknown S K) : CanonicalUnknown S K :=
  (n07aAngularL2SequenceBand hK n U.1,
    (if 0 = n then U.2.1 else 0,
      if 1 = n then U.2.2.1 else 0,
      if 0 = n then U.2.2.2 else 0))

@[simp] theorem n07aAngularUnknownBand_field (hK : ∀ m, K.left m < K.right m)
    (n : ℕ) (U : CanonicalUnknown S K) (m : ℕ) :
    (n07aAngularUnknownBand hK n U).1 m = n07aAngularBand m (hK m) n (U.1 m) := rfl

@[simp] theorem n07aAngularUnknownBand_left (hK : ∀ m, K.left m < K.right m)
    (n : ℕ) (U : CanonicalUnknown S K) :
    (n07aAngularUnknownBand hK n U).2.1 = if 0 = n then U.2.1 else 0 := rfl

@[simp] theorem n07aAngularUnknownBand_border (hK : ∀ m, K.left m < K.right m)
    (n : ℕ) (U : CanonicalUnknown S K) :
    (n07aAngularUnknownBand hK n U).2.2.1 = if 1 = n then U.2.2.1 else 0 := rfl

@[simp] theorem n07aAngularUnknownBand_auxiliary (hK : ∀ m, K.left m < K.right m)
    (n : ℕ) (U : CanonicalUnknown S K) :
    (n07aAngularUnknownBand hK n U).2.2.2 = if 0 = n then U.2.2.2 else 0 := rfl

variable {T : MaterialData} {V : VolumeModelData S K}

theorem n07aAngularLevelBand_forget (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s n : ℕ) (F : V.level γ w s) :
    V.forget γ w s (n07aAngularLevelBand hV γ w hK s n F) =
      n07aAngularSequenceBand hK n (V.forget γ w s F) := by
  funext m
  rw [hV.2.2.2, n07aAngularSequenceBand_apply, hV.2.2.2,
    n07aAngularLevelBand_apply, map_smul]

theorem n07aAngularSequenceBand_volumeMember (hV : IsVolumeModel T S K V)
    (hK : ∀ m, K.left m < K.right m) {γ w : ℝ} {s : ℕ}
    {f : CanonicalSequence S K} (hf : VolumeMember S K V γ w s f) (n : ℕ) :
    VolumeMember S K V γ w s (n07aAngularSequenceBand hK n f) := by
  obtain ⟨F, hF⟩ := hf
  refine ⟨n07aAngularLevelBand hV γ w hK s n F, ?_⟩
  rw [n07aAngularLevelBand_forget, hF]

end ContinuousFlexibility.Statements
