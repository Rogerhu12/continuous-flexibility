import ContinuousFlexibility.Analysis.N07aAngularGraph
import ContinuousFlexibility.Analysis.SpacesTraceRestriction

/-!
# Forgetting a nonnegative material weight in the actual source graph

The physical source stays fixed.  Its complete angular jet is multiplied
on piece `m` by the actual scalar `M(sample(cell m)) ^ (-t)`.  Since the
material function is at least one, this map is contractive for `t ≥ 0`.
No comparison of unrelated model norms is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aMaterialEmbeddingLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _

local instance n07aMaterialEmbeddingLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem n07aAngularMaterialFactor_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    |T.M (T.sample (K.cell m)) ^ (-t)| ≤ 1 := by
  have hM : 1 ≤ T.M (T.sample (K.cell m)) :=
    (hT.2.1 _ (spaces_trace_sample_mem hD hT (K.cell m))).2.2.2
  rw [abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hM) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hM (neg_nonpos.mpr ht)

private def n07aAngularMaterialToZeroJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {t : ℝ} (ht : 0 ≤ t) {s : ℕ} (F : CanonicalVolumeJets S K s) :
    CanonicalVolumeJets S K s :=
  ⟨fun m => (T.M (T.sample (K.cell m)) ^ (-t)) • F m,
    (lp.memℓp F).mono' (fun m => by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right
        (n07aAngularMaterialFactor_bound hD hT ht m) (norm_nonneg (F m))).trans_eq
          (one_mul _))⟩

private theorem n07aAngularMaterialToZeroJets_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {t : ℝ} (ht : 0 ≤ t) {s : ℕ} (F : CanonicalVolumeJets S K s)
    (m : ℕ) (j : Fin (s + 1)) :
    n07aAngularMaterialToZeroJets hD hT ht F m j =
      (T.M (T.sample (K.cell m)) ^ (-t)) • F m j :=
  PiLp.smul_apply (fun _ : Fin (s + 1) => CanonicalL2 S K m) _ (F m) j

private theorem n07aAngularMaterialToZeroJets_graph
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t) {s : ℕ}
    (F : V.level γ t s) :
    n07aAngularMaterialToZeroJets hD hT ht F.val ∈ canonicalVolumeGraph S K s := by
  have hscale (m : ℕ) :
      (T.M (T.sample (K.cell m)) ^ (-t)) • F.val ∈ canonicalVolumeGraph S K s := by
    rw [← hV.1 γ t s]
    exact (V.level γ t s).smul_mem _ F.property
  constructor
  · intro m
    simpa only [n07aAngularMaterialToZeroJets_apply, lp.coeFn_smul,
      Pi.smul_apply, PiLp.smul_apply] using (hscale m).1 m
  · intro m j
    simpa only [n07aAngularMaterialToZeroJets_apply, lp.coeFn_smul,
      Pi.smul_apply, PiLp.smul_apply] using (hscale m).2 m j

/-- The same genuine source, now viewed without its nonnegative material weight. -/
def n07aAngularMaterialToZero
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t) {s : ℕ}
    (F : V.level γ t s) : V.level γ 0 s :=
  ⟨n07aAngularMaterialToZeroJets hD hT ht F.val, by
    rw [← SetLike.mem_coe, hV.1 γ 0 s]
    exact n07aAngularMaterialToZeroJets_graph hD hT hV ht F⟩

@[simp] theorem n07aAngularMaterialToZero_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t) {s : ℕ}
    (F : V.level γ t s) (m : ℕ) (j : Fin (s + 1)) :
    (n07aAngularMaterialToZero hD hT hV ht F).val m j =
      (T.M (T.sample (K.cell m)) ^ (-t)) • F.val m j :=
  n07aAngularMaterialToZeroJets_apply hD hT ht F.val m j

theorem n07aAngularMaterialToZero_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t) {s : ℕ}
    (F : V.level γ t s) : ‖n07aAngularMaterialToZero hD hT hV ht F‖ ≤ ‖F‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe F]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro m
  change ‖(T.M (T.sample (K.cell m)) ^ (-t)) • F.val m‖ ≤ ‖F.val m‖
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right
    (n07aAngularMaterialFactor_bound hD hT ht m) (norm_nonneg _)).trans_eq (one_mul _)

theorem n07aAngularMaterialToZero_forget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t) {s : ℕ}
    (F : V.level γ t s) :
    V.forget γ 0 s (n07aAngularMaterialToZero hD hT hV ht F) = V.forget γ t s F := by
  funext m
  rw [hV.2.2.2, hV.2.2.2, n07aAngularMaterialToZero_apply]
  simp only [neg_zero, Real.rpow_zero, one_mul, smul_smul, mul_comm]

/-- Dropping material and angular orders gives the actual base input to N06. -/
def n07aAngularMaterialToBase
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t)
    {b s : ℕ} (hbs : b ≤ s) (F : V.level γ t s) : V.level γ 0 b :=
  n07aAngularLevelTruncate hV γ 0 hbs (n07aAngularMaterialToZero hD hT hV ht F)

theorem n07aAngularMaterialToBase_forget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t)
    {b s : ℕ} (hbs : b ≤ s) (F : V.level γ t s) :
    V.forget γ 0 b (n07aAngularMaterialToBase hD hT hV ht hbs F) = V.forget γ t s F := by
  rw [n07aAngularMaterialToBase, n07aAngularLevelTruncate_forget,
    n07aAngularMaterialToZero_forget]

theorem n07aAngularMaterialToBase_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} (ht : 0 ≤ t)
    {b s : ℕ} (hbs : b ≤ s) (F : V.level γ t s) :
    ‖n07aAngularMaterialToBase hD hT hV ht hbs F‖ ≤ ‖F‖ :=
  (n07aAngularLevelTruncate_norm_le hV γ 0 hbs _).trans
    (n07aAngularMaterialToZero_norm_le hD hT hV ht F)

end ContinuousFlexibility.Statements
