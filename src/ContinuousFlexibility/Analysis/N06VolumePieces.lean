import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Finite piece cores in the actual canonical source space

The weak angular jet equations are imposed separately on each cylinder.
Consequently cutting off whole cylinders preserves the original source
submodule. Its finite piece core is dense in its own Banach norm. No
replacement of the source by an abstract sequence space is used here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}

theorem n06Volume_single_mem (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s m : ℕ) (v : V.level γ t s) :
    lp.single 2 m (v.val m) ∈ V.level γ t s := by
  have hv : v.val ∈ canonicalVolumeGraph S K s := by
    rw [← hV.1 γ t s]
    exact v.property
  have hz : (0 : CanonicalVolumeJets S K s) ∈ canonicalVolumeGraph S K s := by
    rw [← hV.1 γ t s]
    exact (V.level γ t s).zero_mem
  rw [← SetLike.mem_coe, hV.1 γ t s]
  constructor
  · intro n
    by_cases hn : n = m
    · subst n
      simpa only [lp.single_apply_self] using hv.1 m
    · simpa only [lp.single_apply_ne _ _ _ hn, lp.coeFn_zero, Pi.zero_apply]
        using hz.1 n
  · intro n j
    by_cases hn : n = m
    · subst n
      simpa only [lp.single_apply_self] using hv.2 m j
    · simpa only [lp.single_apply_ne _ _ _ hn, lp.coeFn_zero, Pi.zero_apply]
        using hz.2 n j

/-- Projection to one whole physical cylinder, including every angular jet. -/
def n06VolumePiece (hV : IsVolumeModel T S K V) (γ t : ℝ) (s m : ℕ) :
    V.level γ t s →L[ℝ] V.level γ t s :=
  ((lp.singleContinuousLinearMap ℝ
    (fun n => PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K n)) 2 m).comp
      ((lp.evalCLM ℝ
        (fun n => PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K n)) 2 m).comp
          (V.level γ t s).subtypeL)).codRestrict (V.level γ t s)
    (fun v => n06Volume_single_mem hV γ t s m v)

theorem n06VolumePiece_val (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s m : ℕ) (v : V.level γ t s) :
    (n06VolumePiece hV γ t s m v).val = lp.single 2 m (v.val m) := rfl

theorem n06VolumePiece_norm (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s m : ℕ) (v : V.level γ t s) :
    ‖n06VolumePiece hV γ t s m v‖ = ‖v.val m‖ := by
  change ‖(n06VolumePiece hV γ t s m v).val‖ = _
  rw [n06VolumePiece_val, lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]

theorem n06VolumePiece_norm_le (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s m : ℕ) (v : V.level γ t s) :
    ‖n06VolumePiece hV γ t s m v‖ ≤ ‖v‖ := by
  rw [n06VolumePiece_norm]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) v.val m

theorem n06VolumePiece_forget (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s m n : ℕ) (v : V.level γ t s) :
    V.forget γ t s (n06VolumePiece hV γ t s m v) n =
      if n = m then V.forget γ t s v n else 0 := by
  rw [hV.2.2.2 γ t s, n06VolumePiece_val]
  by_cases hn : n = m
  · subst n
    rw [ite_eq_left rfl, lp.single_apply_self, hV.2.2.2 γ t s]
  · rw [ite_eq_right hn, lp.single_apply_ne _ _ _ hn]
    simp only [PiLp.zero_apply, smul_zero]

/-- The core of sources supported on finitely many cylinders. The angular
regularity remains exactly that of the chosen canonical source level. -/
def n06VolumeFinitePieceCore (γ t : ℝ) (s : ℕ) : Submodule ℝ (V.level γ t s) where
  carrier := {v | ∃ I : Finset ℕ, ∀ m, m ∉ I → v.val m = 0}
  zero_mem' := by
    refine ⟨∅, ?_⟩
    intro m _
    change (0 : CanonicalVolumeJets S K s) m = 0
    simp only [lp.coeFn_zero, Pi.zero_apply]
  add_mem' := by
    rintro u v ⟨I, hI⟩ ⟨J, hJ⟩
    refine ⟨I ∪ J, ?_⟩
    intro m hm
    have hI' : m ∉ I := fun h => hm (Finset.mem_union_left J h)
    have hJ' : m ∉ J := fun h => hm (Finset.mem_union_right I h)
    change (u.val + v.val) m = 0
    rw [lp.coeFn_add, Pi.add_apply, hI m hI', hJ m hJ', add_zero]
  smul_mem' := by
    rintro a v ⟨I, hI⟩
    refine ⟨I, ?_⟩
    intro m hm
    change (a • v.val) m = 0
    rw [lp.coeFn_smul, Pi.smul_apply, hI m hm, smul_zero]

theorem n06VolumePiece_mem_finitePieceCore (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s m : ℕ) (v : V.level γ t s) :
    n06VolumePiece hV γ t s m v ∈ n06VolumeFinitePieceCore γ t s := by
  refine ⟨{m}, ?_⟩
  intro n hn
  rw [n06VolumePiece_val]
  exact lp.single_apply_ne _ _ _ (by simpa only [Finset.mem_singleton] using hn)

/-- The cylinder decomposition converges in the norm of the original source. -/
theorem n06VolumePiece_hasSum (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s : ℕ) (v : V.level γ t s) :
    HasSum (fun m => n06VolumePiece hV γ t s m v) v := by
  change Tendsto (fun I : Finset ℕ => ∑ m ∈ I, n06VolumePiece hV γ t s m v)
    atTop (𝓝 v)
  apply tendsto_subtype_rng.mpr
  have he (I : Finset ℕ) :
      (∑ m ∈ I, n06VolumePiece hV γ t s m v).val =
        ∑ m ∈ I, lp.single 2 m (v.val m) := by
    change (V.level γ t s).subtype (∑ m ∈ I, n06VolumePiece hV γ t s m v) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun m _ => n06VolumePiece_val hV γ t s m v)
  simpa only [HasSum, SummationFilter.unconditional_filter, he] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) v.val)

theorem n06VolumeFinitePieceCore_dense (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s : ℕ) :
    Dense (n06VolumeFinitePieceCore (V := V) γ t s : Set (V.level γ t s)) := by
  intro v
  have hv : v ∈ (n06VolumeFinitePieceCore (V := V) γ t s).topologicalClosure := by
    apply (n06VolumeFinitePieceCore (V := V) γ t s).isClosed_topologicalClosure.mem_of_tendsto
      (n06VolumePiece_hasSum hV γ t s v)
    apply Filter.Eventually.of_forall
    intro I
    apply Submodule.sum_mem
    intro m _
    exact (n06VolumeFinitePieceCore (V := V) γ t s).le_topologicalClosure
      (n06VolumePiece_mem_finitePieceCore hV γ t s m v)
  change v ∈ ((n06VolumeFinitePieceCore (V := V) γ t s).topologicalClosure :
    Set (V.level γ t s)) at hv
  rw [Submodule.topologicalClosure_coe] at hv
  exact hv

end ContinuousFlexibility.Statements
