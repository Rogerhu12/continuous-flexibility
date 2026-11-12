import ContinuousFlexibility.Analysis.N07aAngularBandNorm
import ContinuousFlexibility.Analysis.N07aVolumeCell
import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets

/-!
# A true weighted source level from one band of a canonical sequence

The prescribed weak angular derivatives are the already constructed band
derivatives.  An actual outer L² majorant gives their square summability
after the material and height weights are applied.  The forgotten source
is exactly the original band, on every canonical piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

set_option backward.isDefEq.respectTransparency false

local instance n07aSequenceBandLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aSequenceBandLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem n07aAngularScaledBandJets_graph
    (hI : ∀ m, K.left m < K.right m) (s n : ℕ)
    (f : CanonicalSequence S K) (hf : ∀ m, n07aAngularReflection m (f m) = f m)
    (c : ℕ → ℝ) (v : CanonicalVolumeJets S K s)
    (hv : ∀ m (k : Fin (s + 1)), v m k =
      c m • n07aAngularBandDerivative m (hI m) n k.val (f m)) :
    v ∈ canonicalVolumeGraph S K s := by
  constructor
  · intro m
    have he := (n07aAngularReflection_fixed_iff m _).mpr
      (n07aAngularBand_even m (hI m) n ((n07aAngularReflection_fixed_iff m _).mp (hf m)))
    have hs : n07aAngularReflection m (c m • n07aAngularBand m (hI m) n (f m)) =
        c m • n07aAngularBand m (hI m) n (f m) := by rw [map_smul, he]
    simpa only [hv m 0, Fin.val_zero, n07aAngularBandDerivative_zero] using
      (n07aAngularReflection_fixed_iff m _).mp hs
  · intro m k
    rw [hv m 0, hv m k, Fin.val_zero, n07aAngularBandDerivative_zero]
    apply (n07a_weakCanonicalMixed_zero_radial_iff _ _ k.val).mp
    exact ((n07a_weakCanonicalMixed_zero_radial_iff _ _ k.val).mpr
      (n07aAngularBandDerivative_weak m (hI m) n k.val (f m))).smul (c m)

theorem n07aAngularWeightedBandPiece_norm
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (γ t : ℝ) (hI : ∀ m, K.left m < K.right m) (s n m : ℕ)
    (u : CanonicalL2 S K m) :
    ‖(n07aVolumeWeight T K γ t m)⁻¹ • n07aAngularBandPieceLift m (hI m) s n u‖ =
      (n07aVolumeWeight T K γ t m)⁻¹ * Real.sqrt (n07aAngularJetWeightSq s n) *
        ‖n07aAngularBand m (hI m) n u‖ := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (n07aVolumeWeight_pos hD hT γ t m)), n07aAngularBandPieceLift_norm]
  exact (mul_assoc _ _ _).symm

def n07aAngularSequenceBandLift
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ)
    (hI : ∀ m, K.left m < K.right m) (s n : ℕ)
    (f : CanonicalSequence S K) (hf : ∀ m, n07aAngularReflection m (f m) = f m)
    (a : lp (fun _ : ℕ => ℝ) 2)
    (ha : ∀ m, (n07aVolumeWeight T K γ t m)⁻¹ * Real.sqrt (n07aAngularJetWeightSq s n) *
      ‖n07aAngularBand m (hI m) n (f m)‖ ≤ ‖a m‖) : V.level γ t s := by
  let v : CanonicalVolumeJets S K s :=
    ⟨fun m => (n07aVolumeWeight T K γ t m)⁻¹ • n07aAngularBandPieceLift m (hI m) s n (f m),
      (lp.memℓp a).mono' (fun m => by
        rw [n07aAngularWeightedBandPiece_norm hD hT]
        exact ha m)⟩
  refine ⟨v, ?_⟩
  rw [← SetLike.mem_coe, hV.1 γ t s]
  apply n07aAngularScaledBandJets_graph hI s n f hf
    (fun m => (n07aVolumeWeight T K γ t m)⁻¹) v
  intro m k
  change ((n07aVolumeWeight T K γ t m)⁻¹ •
    n07aAngularBandPieceLift m (hI m) s n (f m)) k = _
  rw [PiLp.smul_apply, n07aAngularBandPieceLift_apply]

theorem n07aAngularSequenceBandLift_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ)
    (hI : ∀ m, K.left m < K.right m) (s n : ℕ)
    (f : CanonicalSequence S K) (hf : ∀ m, n07aAngularReflection m (f m) = f m)
    (a : lp (fun _ : ℕ => ℝ) 2)
    (ha : ∀ m, (n07aVolumeWeight T K γ t m)⁻¹ * Real.sqrt (n07aAngularJetWeightSq s n) *
      ‖n07aAngularBand m (hI m) n (f m)‖ ≤ ‖a m‖) (m : ℕ) (k : Fin (s + 1)) :
    (n07aAngularSequenceBandLift hD hT hV γ t hI s n f hf a ha).val m k =
      (n07aVolumeWeight T K γ t m)⁻¹ • n07aAngularBandDerivative m (hI m) n k.val (f m) := by
  change ((n07aVolumeWeight T K γ t m)⁻¹ •
    n07aAngularBandPieceLift m (hI m) s n (f m)) k = _
  rw [PiLp.smul_apply, n07aAngularBandPieceLift_apply]

theorem n07aAngularSequenceBandLift_forget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ)
    (hI : ∀ m, K.left m < K.right m) (s n : ℕ)
    (f : CanonicalSequence S K) (hf : ∀ m, n07aAngularReflection m (f m) = f m)
    (a : lp (fun _ : ℕ => ℝ) 2)
    (ha : ∀ m, (n07aVolumeWeight T K γ t m)⁻¹ * Real.sqrt (n07aAngularJetWeightSq s n) *
      ‖n07aAngularBand m (hI m) n (f m)‖ ≤ ‖a m‖) :
    V.forget γ t s (n07aAngularSequenceBandLift hD hT hV γ t hI s n f hf a ha) =
      fun m => n07aAngularBand m (hI m) n (f m) := by
  funext m
  rw [n07aVolume_forget_apply hV, n07aAngularSequenceBandLift_apply,
    Fin.val_zero, n07aAngularBandDerivative_zero, smul_smul,
    mul_inv_cancel₀ (n07aVolumeWeight_pos hD hT γ t m).ne', one_smul]

theorem n07aAngularSequenceBandLift_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ)
    (hI : ∀ m, K.left m < K.right m) (s n : ℕ)
    (f : CanonicalSequence S K) (hf : ∀ m, n07aAngularReflection m (f m) = f m)
    (a : lp (fun _ : ℕ => ℝ) 2)
    (ha : ∀ m, (n07aVolumeWeight T K γ t m)⁻¹ * Real.sqrt (n07aAngularJetWeightSq s n) *
      ‖n07aAngularBand m (hI m) n (f m)‖ ≤ ‖a m‖) :
    ‖n07aAngularSequenceBandLift hD hT hV γ t hI s n f hf a ha‖ ≤ ‖a‖ := by
  rw [← Submodule.norm_coe]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro m
  change ‖(n07aVolumeWeight T K γ t m)⁻¹ • n07aAngularBandPieceLift m (hI m) s n (f m)‖ ≤ _
  rw [n07aAngularWeightedBandPiece_norm hD hT]
  exact ha m

end ContinuousFlexibility.Analysis
