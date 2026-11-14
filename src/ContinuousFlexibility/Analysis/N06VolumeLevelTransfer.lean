module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Exact isometries between weight labels of the canonical jet model

The underlying weak-jet graph is identical at every material and height
weight. Its norm is inherited from the same canonical lp space. The
physical forget maps retain their different scalar weights explicitly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}

private theorem n06VolumeLevel_mem_transfer (hV : IsVolumeModel T S K V)
    (γ t γ' t' : ℝ) (s : ℕ) {v : CanonicalVolumeJets S K s}
    (hv : v ∈ V.level γ t s) : v ∈ V.level γ' t' s := by
  have hg : v ∈ canonicalVolumeGraph S K s := by
    rw [← hV.1 γ t s]
    exact hv
  rw [← SetLike.mem_coe, hV.1 γ' t' s]
  exact hg

/-- The identity on every stored canonical jet, as an actual linear isometry. -/
def n06VolumeLevelEquiv (hV : IsVolumeModel T S K V)
    (γ t γ' t' : ℝ) (s : ℕ) : V.level γ t s ≃ₗᵢ[ℝ] V.level γ' t' s where
  toFun F := ⟨F.val, n06VolumeLevel_mem_transfer hV γ t γ' t' s F.property⟩
  invFun F := ⟨F.val, n06VolumeLevel_mem_transfer hV γ' t' γ t s F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp] theorem n06VolumeLevelEquiv_val (hV : IsVolumeModel T S K V)
    (γ t γ' t' : ℝ) (s : ℕ) (F : V.level γ t s) :
    (n06VolumeLevelEquiv hV γ t γ' t' s F).val = F.val := rfl

theorem n06VolumeLevelEquiv_forget (hV : IsVolumeModel T S K V)
    (γ t γ' t' : ℝ) (s : ℕ) (F : V.level γ t s) (m : ℕ) :
    V.forget γ' t' s (n06VolumeLevelEquiv hV γ t γ' t' s F) m =
      (T.M (T.sample (K.cell m)) ^ (-t') * T.H (T.sample (K.cell m)) ^ γ') • F.val m 0 := by
  rw [hV.2.2.2, n06VolumeLevelEquiv_val]

/-- Removing a material-loss label divides the physical zeroth field by
the exact corresponding material factor; no norm or angular order changes. -/
theorem n06VolumeLevelEquiv_material_forget (hV : IsVolumeModel T S K V)
    (β loss : ℝ) (s : ℕ) (F : V.level β (-loss) s) (m : ℕ) :
    V.forget β (-loss) s F m = T.M (T.sample (K.cell m)) ^ loss •
      V.forget β 0 s (n06VolumeLevelEquiv hV β (-loss) β 0 s F) m := by
  rw [hV.2.2.2, n06VolumeLevelEquiv_forget]
  simp only [neg_neg, neg_zero, Real.rpow_zero, one_mul, mul_smul]

end ContinuousFlexibility.Statements
