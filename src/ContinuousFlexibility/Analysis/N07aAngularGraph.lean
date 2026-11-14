module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Data.Fin.Embedding

/-!
# The actual canonical angular graph across Sobolev orders

The maps in this file truncate the derivative coordinates of the prescribed
outer `lp` and inner `PiLp` spaces. They preserve the actual weak derivative
relations and angular reflection in `canonicalVolumeGraph`. No spectral or
regularity certificate is added to `IsVolumeModel`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal BigOperators

variable {S : PhysicalSpacesData} {K : CanonicalData S}

/-- The inclusion of derivative orders in a larger finite jet. -/
def n07aAngularOrderEmbedding {s t : ℕ} (hst : s ≤ t) :
    Fin (s + 1) ↪ Fin (t + 1) :=
  Fin.castLEEmb (Nat.succ_le_succ hst)

@[simp] theorem n07aAngularOrderEmbedding_val {s t : ℕ} (hst : s ≤ t)
    (j : Fin (s + 1)) : (n07aAngularOrderEmbedding hst j).val = j.val := rfl

@[simp] theorem n07aAngularOrderEmbedding_zero {s t : ℕ} (hst : s ≤ t) :
    n07aAngularOrderEmbedding hst 0 = 0 := by
  exact Fin.ext rfl

/-- Truncation of the actual finite Hilbert jet on one canonical piece. -/
def n07aAngularPieceTruncate (m : ℕ) {s t : ℕ} (hst : s ≤ t)
    (v : PiLp 2 (fun _ : Fin (t + 1) => CanonicalL2 S K m)) :
    PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) :=
  WithLp.toLp 2 (fun j => v (n07aAngularOrderEmbedding hst j))

@[simp] theorem n07aAngularPieceTruncate_apply (m : ℕ) {s t : ℕ} (hst : s ≤ t)
    (v : PiLp 2 (fun _ : Fin (t + 1) => CanonicalL2 S K m)) (j : Fin (s + 1)) :
    n07aAngularPieceTruncate m hst v j = v (n07aAngularOrderEmbedding hst j) := by
  simp only [n07aAngularPieceTruncate, PiLp.toLp_apply]

theorem n07aAngularPieceTruncate_norm_le (m : ℕ) {s t : ℕ} (hst : s ≤ t)
    (v : PiLp 2 (fun _ : Fin (t + 1) => CanonicalL2 S K m)) :
    ‖n07aAngularPieceTruncate m hst v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : Fin (s + 1), ‖n07aAngularPieceTruncate m hst v j‖ ^ 2) =
        ∑ j ∈ Finset.univ.map (n07aAngularOrderEmbedding hst), ‖v j‖ ^ 2 := by
      simp only [Finset.sum_map, n07aAngularPieceTruncate_apply]
    _ ≤ ∑ j : Fin (t + 1), ‖v j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)

private def n07aAngularJetsTruncateFun {s t : ℕ} (hst : s ≤ t)
    (v : CanonicalVolumeJets S K t) : CanonicalVolumeJets S K s :=
  ⟨fun m => n07aAngularPieceTruncate m hst (v m),
    (lp.memℓp v).mono' (fun m => n07aAngularPieceTruncate_norm_le m hst (v m))⟩

private theorem n07aAngularJetsTruncateFun_apply {s t : ℕ} (hst : s ≤ t)
    (v : CanonicalVolumeJets S K t) (m : ℕ) (j : Fin (s + 1)) :
    n07aAngularJetsTruncateFun hst v m j = v m (n07aAngularOrderEmbedding hst j) :=
  n07aAngularPieceTruncate_apply m hst (v m) j

private theorem n07aAngularJetsTruncateFun_norm_le {s t : ℕ} (hst : s ≤ t)
    (v : CanonicalVolumeJets S K t) : ‖n07aAngularJetsTruncateFun hst v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro m
  exact n07aAngularPieceTruncate_norm_le m hst (v m)

/-- Contractive restriction of every piece of the actual angular jet. -/
def n07aAngularJetsTruncate {s t : ℕ} (hst : s ≤ t) :
    CanonicalVolumeJets S K t →L[ℝ] CanonicalVolumeJets S K s :=
  (show CanonicalVolumeJets S K t →ₗ[ℝ] CanonicalVolumeJets S K s from
    { toFun := n07aAngularJetsTruncateFun hst
      map_add' := by
        intro v w
        apply lp.ext
        funext m
        apply PiLp.ext
        intro j
        simp only [n07aAngularJetsTruncateFun_apply, lp.coeFn_add, Pi.add_apply,
          PiLp.add_apply]
      map_smul' := by
        intro c v
        apply lp.ext
        funext m
        apply PiLp.ext
        intro j
        simp only [n07aAngularJetsTruncateFun_apply, lp.coeFn_smul, Pi.smul_apply,
          PiLp.smul_apply, RingHom.id_apply] }).mkContinuous 1 (fun v => by
    simpa only [one_mul, LinearMap.coe_mk, AddHom.coe_mk] using
      n07aAngularJetsTruncateFun_norm_le hst v)

@[simp] theorem n07aAngularJetsTruncate_apply {s t : ℕ} (hst : s ≤ t)
    (v : CanonicalVolumeJets S K t) (m : ℕ) (j : Fin (s + 1)) :
    n07aAngularJetsTruncate hst v m j = v m (n07aAngularOrderEmbedding hst j) :=
  n07aAngularJetsTruncateFun_apply hst v m j

theorem n07aAngularJetsTruncate_norm_le {s t : ℕ} (hst : s ≤ t)
    (v : CanonicalVolumeJets S K t) : ‖n07aAngularJetsTruncate hst v‖ ≤ ‖v‖ :=
  n07aAngularJetsTruncateFun_norm_le hst v

theorem n07aAngularJetsTruncate_mem_graph {s t : ℕ} (hst : s ≤ t)
    {v : CanonicalVolumeJets S K t} (hv : v ∈ canonicalVolumeGraph S K t) :
    n07aAngularJetsTruncate hst v ∈ canonicalVolumeGraph S K s := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa only [n07aAngularJetsTruncate_apply, n07aAngularOrderEmbedding_zero] using hv.1 m
  · intro m j
    simpa only [n07aAngularJetsTruncate_apply, n07aAngularOrderEmbedding_zero,
      n07aAngularOrderEmbedding_val] using hv.2 m (n07aAngularOrderEmbedding hst j)

variable {T : MaterialData} {V : VolumeModelData S K}

/-- Truncation on the given volume model, obtained from its true graph identity. -/
def n07aAngularLevelTruncate (hV : IsVolumeModel T S K V) (γ w : ℝ)
    {s t : ℕ} (hst : s ≤ t) : V.level γ w t →L[ℝ] V.level γ w s :=
  ((n07aAngularJetsTruncate hst).comp (V.level γ w t).subtypeL).codRestrict
    (V.level γ w s) (by
      intro v
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      apply (show n07aAngularJetsTruncate hst v.val ∈ canonicalVolumeGraph S K s →
          n07aAngularJetsTruncate hst v.val ∈ V.level γ w s from by
        rw [← SetLike.mem_coe, hV.1 γ w s]
        exact id)
      apply n07aAngularJetsTruncate_mem_graph hst
      rw [← hV.1 γ w t]
      exact v.property)

@[simp] theorem n07aAngularLevelTruncate_val (hV : IsVolumeModel T S K V) (γ w : ℝ)
    {s t : ℕ} (hst : s ≤ t) (v : V.level γ w t) :
    (n07aAngularLevelTruncate hV γ w hst v).val = n07aAngularJetsTruncate hst v.val := by
  simp only [n07aAngularLevelTruncate, ContinuousLinearMap.coe_codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

@[simp] theorem n07aAngularLevelTruncate_apply (hV : IsVolumeModel T S K V) (γ w : ℝ)
    {s t : ℕ} (hst : s ≤ t) (v : V.level γ w t) (m : ℕ) (j : Fin (s + 1)) :
    (n07aAngularLevelTruncate hV γ w hst v).val m j =
      v.val m (n07aAngularOrderEmbedding hst j) := by
  rw [n07aAngularLevelTruncate_val, n07aAngularJetsTruncate_apply]

theorem n07aAngularLevelTruncate_norm_le (hV : IsVolumeModel T S K V) (γ w : ℝ)
    {s t : ℕ} (hst : s ≤ t) (v : V.level γ w t) :
    ‖n07aAngularLevelTruncate hV γ w hst v‖ ≤ ‖v‖ := by
  rw [← Submodule.norm_coe (n07aAngularLevelTruncate hV γ w hst v),
    ← Submodule.norm_coe v, n07aAngularLevelTruncate_val]
  exact n07aAngularJetsTruncate_norm_le hst v.val

/-- All angular orders describe the same physical source after forgetting jets. -/
theorem n07aAngularLevelTruncate_forget (hV : IsVolumeModel T S K V) (γ w : ℝ)
    {s t : ℕ} (hst : s ≤ t) (v : V.level γ w t) :
    V.forget γ w s (n07aAngularLevelTruncate hV γ w hst v) = V.forget γ w t v := by
  funext m
  rw [hV.2.2.2 γ w s, hV.2.2.2 γ w t, n07aAngularLevelTruncate_apply,
    n07aAngularOrderEmbedding_zero]

theorem n07aAngularLevelTruncate_injective (hV : IsVolumeModel T S K V) (γ w : ℝ)
    {s t : ℕ} (hst : s ≤ t) : Function.Injective (n07aAngularLevelTruncate hV γ w hst) := by
  intro v u h
  apply hV.2.2.1 γ w t
  have he := congrArg (V.forget γ w s) h
  simpa only [n07aAngularLevelTruncate_forget] using he

theorem n07aAngularLevelTruncate_refl (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (s : ℕ) (v : V.level γ w s) : n07aAngularLevelTruncate hV γ w le_rfl v = v := by
  apply hV.2.2.1 γ w s
  exact n07aAngularLevelTruncate_forget hV γ w le_rfl v

theorem n07aAngularLevelTruncate_comp (hV : IsVolumeModel T S K V) (γ w : ℝ)
    {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) (v : V.level γ w t) :
    n07aAngularLevelTruncate hV γ w hrs (n07aAngularLevelTruncate hV γ w hst v) =
      n07aAngularLevelTruncate hV γ w (hrs.trans hst) v := by
  apply hV.2.2.1 γ w r
  rw [n07aAngularLevelTruncate_forget, n07aAngularLevelTruncate_forget,
    n07aAngularLevelTruncate_forget]

/-- Higher angular membership implies every lower angular membership. -/
theorem n07aAngularVolumeMember_mono (hV : IsVolumeModel T S K V)
    {γ w : ℝ} {s t : ℕ} (hst : s ≤ t) {f : CanonicalSequence S K}
    (hf : VolumeMember S K V γ w t f) : VolumeMember S K V γ w s f := by
  obtain ⟨v, rfl⟩ := hf
  exact ⟨n07aAngularLevelTruncate hV γ w hst v,
    n07aAngularLevelTruncate_forget hV γ w hst v⟩

end ContinuousFlexibility.Statements
