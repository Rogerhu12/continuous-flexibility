import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.SpacesTraceRestriction

/-!
# Actual cell localization and change of volume weights

Every weight level has the same prescribed weak angular graph. Localizing
that graph to one physical piece therefore preserves every angular jet.
The scalar change of weight below preserves the actual forgotten source;
it does not assume an inclusion between different global weighted spaces.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance (γ t : ℝ) (s : ℕ) : NormedAddCommGroup (V.level γ t s) :=
  Submodule.normedAddCommGroup _

local instance (γ t : ℝ) (s : ℕ) : NormedSpace ℝ (V.level γ t s) :=
  Submodule.normedSpace _

/-- The physical multiplier already prescribed by `IsVolumeModel`. -/
def n07aVolumeWeight (T : MaterialData) (K : CanonicalData S)
    (γ t : ℝ) (m : ℕ) : ℝ :=
  T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ

theorem n07aVolumeWeight_pos
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (γ t : ℝ) (m : ℕ) : 0 < n07aVolumeWeight T K γ t m := by
  have hm := spaces_trace_sample_mem hD hT (K.cell m)
  have hpos := hT.2.1 _ hm
  exact mul_pos
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hpos.2.2.2) _)
    (Real.rpow_pos_of_pos hpos.2.1 _)

theorem n07aVolume_forget_apply (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {s : ℕ} (F : V.level γ t s) (m : ℕ) :
    V.forget γ t s F m = n07aVolumeWeight T K γ t m • F.val m 0 :=
  hV.2.2.2 γ t s F m

private theorem n07aVolumeSingle_mem_graph (s m : ℕ)
    (hzero : (0 : CanonicalVolumeJets S K s) ∈ canonicalVolumeGraph S K s)
    {v : CanonicalVolumeJets S K s} (hv : v ∈ canonicalVolumeGraph S K s) :
    lp.single 2 m (v m) ∈ canonicalVolumeGraph S K s := by
  constructor
  · intro n
    by_cases hnm : n = m
    · subst n
      simpa only [lp.single_apply_self] using hv.1 m
    · simpa only [lp.single_apply_ne (E := fun n => PiLp 2
        (fun _ : Fin (s + 1) => CanonicalL2 S K n)) 2 m (v m) hnm, lp.coeFn_zero,
        Pi.zero_apply] using hzero.1 n
  · intro n j
    by_cases hnm : n = m
    · subst n
      simpa only [lp.single_apply_self] using hv.2 m j
    · simpa only [lp.single_apply_ne (E := fun n => PiLp 2
        (fun _ : Fin (s + 1) => CanonicalL2 S K n)) 2 m (v m) hnm, lp.coeFn_zero,
        Pi.zero_apply] using hzero.2 n j

/-- The complete jet on one piece, viewed in any given weight level. -/
def n07aVolumeCell (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) : V.level γ' t' s :=
  ⟨lp.single 2 m (F.val m), by
    rw [← SetLike.mem_coe, hV.1 γ' t' s]
    have hzero : (0 : CanonicalVolumeJets S K s) ∈ canonicalVolumeGraph S K s := by
      rw [← hV.1 γ' t' s]
      exact (V.level γ' t' s).zero_mem
    have hF : F.val ∈ canonicalVolumeGraph S K s := by
      rw [← hV.1 γ t s]
      exact F.property
    exact n07aVolumeSingle_mem_graph s m hzero hF⟩

theorem n07aVolumeCell_val (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) :
    (n07aVolumeCell hV γ' t' m F).val = lp.single 2 m (F.val m) := rfl

theorem n07aVolumeCell_apply_same (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) :
    (n07aVolumeCell hV γ' t' m F).val m = F.val m := by
  rw [n07aVolumeCell_val, lp.single_apply_self]

theorem n07aVolumeCell_apply_ne (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) {n : ℕ} (hnm : n ≠ m) :
    (n07aVolumeCell hV γ' t' m F).val n = 0 := by
  rw [n07aVolumeCell_val]
  exact lp.single_apply_ne (E := fun n => PiLp 2
    (fun _ : Fin (s + 1) => CanonicalL2 S K n)) 2 m (F.val m) hnm

theorem n07aVolumeCell_norm (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) :
    ‖n07aVolumeCell hV γ' t' m F‖ = ‖F.val m‖ := by
  rw [← Submodule.norm_coe, n07aVolumeCell_val]
  exact lp.norm_single (E := fun n => PiLp 2
    (fun _ : Fin (s + 1) => CanonicalL2 S K n))
    (by norm_num : (0 : ℝ≥0∞) < 2) m (F.val m)

theorem n07aVolumeCell_norm_le (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) :
    ‖n07aVolumeCell hV γ' t' m F‖ ≤ ‖F‖ := by
  rw [n07aVolumeCell_norm, ← Submodule.norm_coe F]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) F.val m

theorem n07aVolumeCell_forget (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) :
    V.forget γ' t' s (n07aVolumeCell hV γ' t' m F) =
      Pi.single m (n07aVolumeWeight T K γ' t' m • F.val m 0) := by
  funext n
  rw [n07aVolume_forget_apply hV]
  by_cases hnm : n = m
  · subst n
    rw [n07aVolumeCell_apply_same, Pi.single_eq_same]
  · rw [n07aVolumeCell_apply_ne hV γ' t' m F hnm, PiLp.zero_apply,
      smul_zero, Pi.single_eq_of_ne hnm]

/-- A localized source with unchanged physical value after changing weights. -/
def n07aVolumeCellReweight (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) : V.level γ' t' s :=
  (n07aVolumeWeight T K γ t m / n07aVolumeWeight T K γ' t' m) •
    n07aVolumeCell hV γ' t' m F

theorem n07aVolumeCellReweight_norm (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s) :
    ‖n07aVolumeCellReweight hV γ' t' m F‖ =
      |n07aVolumeWeight T K γ t m / n07aVolumeWeight T K γ' t' m| * ‖F.val m‖ := by
  rw [n07aVolumeCellReweight, norm_smul, Real.norm_eq_abs, n07aVolumeCell_norm]

/-- The equality is in the prescribed sequence of actual `L²` classes. -/
theorem n07aVolumeCellReweight_forget (hV : IsVolumeModel T S K V) (γ' t' : ℝ)
    {γ t : ℝ} {s : ℕ} (m : ℕ) (F : V.level γ t s)
    (hw : n07aVolumeWeight T K γ' t' m ≠ 0) :
    V.forget γ' t' s (n07aVolumeCellReweight hV γ' t' m F) =
      Pi.single m (V.forget γ t s F m) := by
  rw [n07aVolumeCellReweight, map_smul, n07aVolumeCell_forget]
  funext n
  rw [Pi.smul_apply]
  by_cases hnm : n = m
  · subst n
    rw [Pi.single_eq_same, Pi.single_eq_same, n07aVolume_forget_apply hV,
      smul_smul, div_mul_cancel₀ _ hw]
  · rw [Pi.single_eq_of_ne hnm, Pi.single_eq_of_ne hnm, smul_zero]

theorem n07aVolumeCellReweight_eq_of_forget (hV : IsVolumeModel T S K V)
    (γ' t' : ℝ) {γ₁ t₁ γ₂ t₂ : ℝ} {s : ℕ} (m : ℕ)
    (F : V.level γ₁ t₁ s) (G : V.level γ₂ t₂ s)
    (hw : n07aVolumeWeight T K γ' t' m ≠ 0)
    (hFG : V.forget γ₁ t₁ s F = V.forget γ₂ t₂ s G) :
    n07aVolumeCellReweight hV γ' t' m F = n07aVolumeCellReweight hV γ' t' m G := by
  apply hV.2.2.1 γ' t' s
  rw [n07aVolumeCellReweight_forget hV γ' t' m F hw,
    n07aVolumeCellReweight_forget hV γ' t' m G hw, hFG]

end ContinuousFlexibility.Analysis
