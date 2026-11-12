import ContinuousFlexibility.Analysis.N07aAngularEndpointFlux
import ContinuousFlexibility.Analysis.N07aVolumeWeightBounds

/-!
# Positive height weight gives the genuine unweighted canonical sequence

The material envelope already bounds H^γ M^(−t) for every real t and
positive γ. Thus forgetting any such volume level has a true outer ℓ²
representative, as required by the original canonical unknown space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory ContinuousFlexibility.Statements
open scoped ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

theorem n07a_positiveHeightVolume_forget_memℓp
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (hγ : 0 < γ) {s : ℕ}
    (W : V.level γ t s) : Memℓp (V.forget γ t s W) 2 := by
  let bounds := n07a_material_decay_uniform_bound hT hγ (-t)
  let A : ℝ := bounds.choose
  have hA := bounds.choose_spec.1
  have hAb := bounds.choose_spec.2
  have hscaled : Memℓp (A • (W.val : ∀ m, PiLp 2 (fun _ : Fin (s + 1) =>
      CanonicalL2 S K m))) 2 := (lp.memℓp W.val).const_smul A
  apply hscaled.mono'
  intro m
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hA]
  apply (n07aVolume_forget_norm_le hD hT hV W m).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [n07aVolumeWeight, mul_comm] using
    hAb _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))

def n07aPositiveHeightVolumeSequence
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (hγ : 0 < γ) {s : ℕ}
    (W : V.level γ t s) : CanonicalL2Sequence S K :=
  ⟨V.forget γ t s W, n07a_positiveHeightVolume_forget_memℓp hD hT hV hγ W⟩

theorem n07aPositiveHeightVolumeSequence_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (hγ : 0 < γ) {s : ℕ}
    (W : V.level γ t s) (m : ℕ) :
    n07aPositiveHeightVolumeSequence hD hT hV hγ W m = V.forget γ t s W m := rfl

end ContinuousFlexibility.Analysis
