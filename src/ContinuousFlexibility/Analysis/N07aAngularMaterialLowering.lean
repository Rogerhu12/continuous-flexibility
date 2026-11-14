module

public import ContinuousFlexibility.Analysis.N07aAngularMaterialEmbedding

/-!
# Lowering an arbitrary real material order in the same actual volume graph

The original graph is independent of its material label. Relabeling an
intermediate jet and using the proved material-to-zero contraction gives
the actual multiplier `M^(u-t)` for every `u ≤ t`. The final forget map is
exactly the original physical source; no integer restriction is imposed
on the real material loss of N05.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aMaterialLoweringLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _

local instance n07aMaterialLoweringLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

private def n07aAngularMaterialRelabel
    (hV : IsVolumeModel T S K V) {γ t u : ℝ} {s : ℕ}
    (F : V.level γ t s) : V.level γ u s :=
  ⟨F.val, by
    rw [← SetLike.mem_coe, hV.1 γ u s, ← hV.1 γ t s]
    exact F.property⟩

private theorem n07aAngularMaterialRelabel_val
    (hV : IsVolumeModel T S K V) {γ t u : ℝ} {s : ℕ}
    (F : V.level γ t s) :
    (n07aAngularMaterialRelabel (u := u) hV F).val = F.val := rfl

private theorem n07aAngularMaterialRelabel_norm
    (hV : IsVolumeModel T S K V) {γ t u : ℝ} {s : ℕ}
    (F : V.level γ t s) :
    ‖n07aAngularMaterialRelabel (u := u) hV F‖ = ‖F‖ := by
  rw [← Submodule.norm_coe, n07aAngularMaterialRelabel_val, Submodule.norm_coe]

def n07aAngularMaterialLower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t u : ℝ} (hut : u ≤ t) {s : ℕ}
    (F : V.level γ t s) : V.level γ u s :=
  n07aAngularMaterialRelabel hV
    (n07aAngularMaterialToZero hD hT hV (sub_nonneg.mpr hut)
      (n07aAngularMaterialRelabel (u := t - u) hV F))

theorem n07aAngularMaterialLower_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t u : ℝ} (hut : u ≤ t) {s : ℕ}
    (F : V.level γ t s) (m : ℕ) (j : Fin (s + 1)) :
    (n07aAngularMaterialLower hD hT hV hut F).val m j =
      (T.M (T.sample (K.cell m)) ^ (-(t - u))) • F.val m j := by
  simp only [n07aAngularMaterialLower, n07aAngularMaterialRelabel_val,
    n07aAngularMaterialToZero_apply]

theorem n07aAngularMaterialLower_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t u : ℝ} (hut : u ≤ t) {s : ℕ}
    (F : V.level γ t s) :
    ‖n07aAngularMaterialLower hD hT hV hut F‖ ≤ ‖F‖ := by
  simpa only [n07aAngularMaterialLower, n07aAngularMaterialRelabel_norm] using
    n07aAngularMaterialToZero_norm_le hD hT hV (sub_nonneg.mpr hut)
      (n07aAngularMaterialRelabel (u := t - u) hV F)

theorem n07aAngularMaterialLower_forget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t u : ℝ} (hut : u ≤ t) {s : ℕ}
    (F : V.level γ t s) :
    V.forget γ u s (n07aAngularMaterialLower hD hT hV hut F) = V.forget γ t s F := by
  funext m
  have hM : 0 < T.M (T.sample (K.cell m)) :=
    zero_lt_one.trans_le (hT.2.1 _ (spaces_trace_sample_mem hD hT (K.cell m))).2.2.2
  have hscale :
      (T.M (T.sample (K.cell m)) ^ (-u) * T.H (T.sample (K.cell m)) ^ γ) *
        T.M (T.sample (K.cell m)) ^ (-(t - u)) =
      T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ := by
    calc
      _ = (T.M (T.sample (K.cell m)) ^ (-u) *
          T.M (T.sample (K.cell m)) ^ (-(t - u))) *
          T.H (T.sample (K.cell m)) ^ γ := by ring
      _ = _ := by
        have he : -u + -(t - u) = -t := by ring
        rw [← Real.rpow_add hM, he]
  rw [hV.2.2.2, hV.2.2.2, n07aAngularMaterialLower_apply, smul_smul, hscale]

theorem n07a_volumeMember_lower_material
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t u : ℝ} (hut : u ≤ t) {s : ℕ}
    {f : CanonicalSequence S K} (hf : VolumeMember S K V γ t s f) :
    VolumeMember S K V γ u s f := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨n07aAngularMaterialLower hD hT hV hut F,
    (n07aAngularMaterialLower_forget hD hT hV hut F).trans hF⟩

end ContinuousFlexibility.Statements
