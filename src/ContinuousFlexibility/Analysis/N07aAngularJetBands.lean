import ContinuousFlexibility.Analysis.N07aAngularBands
import ContinuousFlexibility.Analysis.N07aAngularGraph

/-!
# Frequency projections on the prescribed canonical volume graph

The actual scalar projection is applied to every derivative coordinate
and every radial component. The resulting contractive operator preserves
the original weak graph and its angular reflection. Its restriction to
each given `VolumeModelData.level` is therefore a genuine orthogonal
projection of that Hilbert space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S}

private def n07aAngularPieceBand (m : ℕ) (hm : K.left m < K.right m) (s n : ℕ)
    (u : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) :
    PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) :=
  WithLp.toLp 2 (fun j => n07aAngularBand m hm n (u j))

private theorem n07aAngularPieceBand_apply (m : ℕ) (hm : K.left m < K.right m) (s n : ℕ)
    (u : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) (j : Fin (s + 1)) :
    n07aAngularPieceBand m hm s n u j = n07aAngularBand m hm n (u j) := by
  simp only [n07aAngularPieceBand, PiLp.toLp_apply]

private theorem n07aAngularPieceBand_norm_le (m : ℕ) (hm : K.left m < K.right m) (s n : ℕ)
    (u : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) :
    ‖n07aAngularPieceBand m hm s n u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _
  rw [n07aAngularPieceBand_apply]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (n07aAngularBand_norm_le m hm n (u j))

private def n07aAngularJetsBandFun (hK : ∀ m, K.left m < K.right m) (s n : ℕ)
    (u : CanonicalVolumeJets S K s) : CanonicalVolumeJets S K s :=
  ⟨fun m => n07aAngularPieceBand m (hK m) s n (u m),
    (lp.memℓp u).mono' (fun m => n07aAngularPieceBand_norm_le m (hK m) s n (u m))⟩

private theorem n07aAngularJetsBandFun_apply (hK : ∀ m, K.left m < K.right m) (s n : ℕ)
    (u : CanonicalVolumeJets S K s) (m : ℕ) (j : Fin (s + 1)) :
    n07aAngularJetsBandFun hK s n u m j = n07aAngularBand m (hK m) n (u m j) :=
  n07aAngularPieceBand_apply m (hK m) s n (u m) j

private theorem n07aAngularJetsBandFun_norm_le (hK : ∀ m, K.left m < K.right m) (s n : ℕ)
    (u : CanonicalVolumeJets S K s) : ‖n07aAngularJetsBandFun hK s n u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro m
  exact n07aAngularPieceBand_norm_le m (hK m) s n (u m)

def n07aAngularJetsBand (hK : ∀ m, K.left m < K.right m) (s n : ℕ) :
    CanonicalVolumeJets S K s →L[ℝ] CanonicalVolumeJets S K s :=
  (show CanonicalVolumeJets S K s →ₗ[ℝ] CanonicalVolumeJets S K s from
    { toFun := n07aAngularJetsBandFun hK s n
      map_add' := by
        intro u v
        apply lp.ext
        funext m
        apply PiLp.ext
        intro j
        simp only [n07aAngularJetsBandFun_apply, lp.coeFn_add, Pi.add_apply,
          PiLp.add_apply, map_add]
      map_smul' := by
        intro c u
        apply lp.ext
        funext m
        apply PiLp.ext
        intro j
        simp only [n07aAngularJetsBandFun_apply, lp.coeFn_smul, Pi.smul_apply,
          PiLp.smul_apply, map_smul, RingHom.id_apply] }).mkContinuous 1 (fun u => by
    simpa only [one_mul, LinearMap.coe_mk, AddHom.coe_mk] using
      n07aAngularJetsBandFun_norm_le hK s n u)

@[simp] theorem n07aAngularJetsBand_apply (hK : ∀ m, K.left m < K.right m) (s n : ℕ)
    (u : CanonicalVolumeJets S K s) (m : ℕ) (j : Fin (s + 1)) :
    n07aAngularJetsBand hK s n u m j = n07aAngularBand m (hK m) n (u m j) :=
  n07aAngularJetsBandFun_apply hK s n u m j

theorem n07aAngularJetsBand_norm_le (hK : ∀ m, K.left m < K.right m) (s n : ℕ)
    (u : CanonicalVolumeJets S K s) : ‖n07aAngularJetsBand hK s n u‖ ≤ ‖u‖ :=
  n07aAngularJetsBandFun_norm_le hK s n u

theorem n07aAngularJetsBand_mem_graph (hK : ∀ m, K.left m < K.right m) (s n : ℕ)
    {u : CanonicalVolumeJets S K s} (hu : u ∈ canonicalVolumeGraph S K s) :
    n07aAngularJetsBand hK s n u ∈ canonicalVolumeGraph S K s := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa only [n07aAngularJetsBand_apply] using n07aAngularBand_even m (hK m) n (hu.1 m)
  · intro m j
    simpa only [n07aAngularJetsBand_apply] using n07aAngularBand_weak m (hK m) n (hu.2 m j)

variable {T : MaterialData} {V : VolumeModelData S K}

def n07aAngularLevelBand (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s n : ℕ) : V.level γ w s →L[ℝ] V.level γ w s :=
  ((n07aAngularJetsBand hK s n).comp (V.level γ w s).subtypeL).codRestrict
    (V.level γ w s) (by
      intro u
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      have hu : u.val ∈ canonicalVolumeGraph S K s := by
        rw [← hV.1 γ w s]
        exact u.property
      have h := n07aAngularJetsBand_mem_graph hK s n hu
      rwa [← hV.1 γ w s] at h)

@[simp] theorem n07aAngularLevelBand_val (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s n : ℕ) (u : V.level γ w s) :
    (n07aAngularLevelBand hV γ w hK s n u).val = n07aAngularJetsBand hK s n u.val := by
  simp only [n07aAngularLevelBand, ContinuousLinearMap.coe_codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

@[simp] theorem n07aAngularLevelBand_apply (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s n : ℕ) (u : V.level γ w s)
    (m : ℕ) (j : Fin (s + 1)) :
    (n07aAngularLevelBand hV γ w hK s n u).val m j = n07aAngularBand m (hK m) n (u.val m j) := by
  rw [n07aAngularLevelBand_val, n07aAngularJetsBand_apply]

theorem n07aAngularLevelBand_norm_le (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s n : ℕ) (u : V.level γ w s) :
    ‖n07aAngularLevelBand hV γ w hK s n u‖ ≤ ‖u‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe u, n07aAngularLevelBand_val]
  exact n07aAngularJetsBand_norm_le hK s n u.val

theorem n07aAngularLevelBand_idempotent (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s n : ℕ) (u : V.level γ w s) :
    n07aAngularLevelBand hV γ w hK s n (n07aAngularLevelBand hV γ w hK s n u) =
      n07aAngularLevelBand hV γ w hK s n u := by
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro j
  simp only [n07aAngularLevelBand_apply, n07aAngularBand_idempotent]

theorem n07aAngularLevelBand_comp_eq_zero (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s : ℕ) {n l : ℕ} (hnl : n ≠ l) (u : V.level γ w s) :
    n07aAngularLevelBand hV γ w hK s n (n07aAngularLevelBand hV γ w hK s l u) = 0 := by
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro j
  simp only [n07aAngularLevelBand_apply, n07aAngularBand_comp_eq_zero m (hK m) hnl,
    ZeroMemClass.coe_zero, Pi.zero_apply, PiLp.zero_apply]

theorem n07aAngularLevelBand_symmetric (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s n : ℕ) (u v : V.level γ w s) :
    inner ℝ (n07aAngularLevelBand hV γ w hK s n u) v =
      inner ℝ u (n07aAngularLevelBand hV γ w hK s n v) := by
  rw [Submodule.coe_inner, Submodule.coe_inner, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro m
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [n07aAngularLevelBand_apply]
  exact n07aAngularBand_symmetric m (hK m) n _ _

theorem n07aAngularLevelBand_orthogonal (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s : ℕ) {n l : ℕ} (hnl : n ≠ l)
    (u v : V.level γ w s) :
    inner ℝ (n07aAngularLevelBand hV γ w hK s n u) (n07aAngularLevelBand hV γ w hK s l v) = 0 := by
  rw [n07aAngularLevelBand_symmetric, n07aAngularLevelBand_comp_eq_zero hV γ w hK s hnl,
    inner_zero_right]

/-- The actual projections detect every coordinate of the original source graph. -/
theorem n07aAngularLevelBand_total (hV : IsVolumeModel T S K V) (γ w : ℝ)
    (hK : ∀ m, K.left m < K.right m) (s : ℕ) (u : V.level γ w s)
    (hu : ∀ n, n07aAngularLevelBand hV γ w hK s n u = 0) : u = 0 := by
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro j
  apply (n07aAngularFourier m (hK m)).injective
  apply lp.ext
  funext q
  have h := congrArg (fun v : V.level γ w s => n07aAngularFourier m (hK m) (v.val m j) q)
    (hu (n07aAngularFrequency q))
  simpa only [n07aAngularLevelBand_apply, n07aAngularBand_coefficient, ite_true,
    ZeroMemClass.coe_zero, lp.coeFn_zero, Pi.zero_apply, PiLp.zero_apply, map_zero] using h

end ContinuousFlexibility.Statements
