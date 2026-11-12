import ContinuousFlexibility.Analysis.N07bCanonicalSourceLift
import ContinuousFlexibility.Analysis.SpacesTraceRestriction

/-!
# Positive-height canonical levels have genuine L² unknown sequences

The prescribed forget factors are uniformly bounded at every positive
height exponent, for every fixed material order. This follows from the
actual material absorption axiom, and makes the forgotten zeroth jet an
element of the canonical unknown Hilbert sequence. It is not a new
assumption on the volume model.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ENNReal

/-- The actual sample factors in the prescribed forget map are bounded. -/
theorem n07b_canonicalSourceFactor_bounded
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (K : CanonicalData S) {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m,
      0 < n07bCanonicalSourceFactor T K γ t m ∧
        n07bCanonicalSourceFactor T K γ t m ≤ C := by
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, hHM, _⟩ := hdata
  obtain ⟨C, hC, hbound, _, _⟩ := hHM (-t) γ hγ
  refine ⟨C, hC, fun m => ?_⟩
  have hs := spaces_trace_sample_mem hD hT (K.cell m)
  have hM : 0 < T.M (T.sample (K.cell m)) :=
    zero_lt_one.trans_le (hpos _ hs).2.2.2
  have hH : 0 < T.H (T.sample (K.cell m)) := (hpos _ hs).2.1
  refine ⟨mul_pos (Real.rpow_pos_of_pos hM _) (Real.rpow_pos_of_pos hH _), ?_⟩
  simpa only [n07bCanonicalSourceFactor, mul_comm] using hbound _ hs

/-- The unweighted canonical unknown sequence exists for every positive
height level; its integrability follows from the actual weighted level. -/
theorem n07b_volume_forget_memℓp
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    {γ : ℝ} (hγ : 0 < γ) (t : ℝ) (s : ℕ) (v : V.level γ t s) :
    Memℓp (V.forget γ t s v) 2 := by
  obtain ⟨C, hC, hfactor⟩ := n07b_canonicalSourceFactor_bounded hD hT K hγ t
  apply ((lp.memℓp v.val).const_smul C).mono'
  intro m
  rw [hV.2.2.2 γ t s]
  change ‖n07bCanonicalSourceFactor T K γ t m • v.val m 0‖ ≤ ‖C • v.val m‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (hfactor m).1, abs_of_pos hC]
  exact mul_le_mul (hfactor m).2 (PiLp.norm_apply_le (v.val m) 0)
    (norm_nonneg _) hC.le

/-- The genuine canonical Hilbert sequence represented by a positive
height volume element. -/
def n07bVolumeUnknownSequence
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    {γ : ℝ} (hγ : 0 < γ) (t : ℝ) (s : ℕ) (v : V.level γ t s) :
    CanonicalL2Sequence S K :=
  ⟨V.forget γ t s v, n07b_volume_forget_memℓp hD hT hV hγ t s v⟩

theorem n07bVolumeUnknownSequence_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    {γ : ℝ} (hγ : 0 < γ) (t : ℝ) (s : ℕ) (v : V.level γ t s) (m : ℕ) :
    n07bVolumeUnknownSequence hD hT hV hγ t s v m = V.forget γ t s v m := rfl

end ContinuousFlexibility.Statements
