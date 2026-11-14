module

public import ContinuousFlexibility.Analysis.N05CanonicalSmoothJets
public import ContinuousFlexibility.Analysis.SpacesTraceRestriction
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite smooth fields in the actual canonical source level

The original N05 smooth jets already satisfy the exact weak angular graph
identities. Each smooth single-column row is divided by the prescribed
material weight and inserted in the selected volume model. A finite sum
then represents the given physical fields in every original canonical
measure. The norm estimate uses their actual angular derivatives and the
finite cylinder measures, with no source-membership premise.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The L2 cost of a pointwise bound on the actual finite canonical strip. -/
def n06CanonicalStripL2Cost (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) : ℝ :=
  (measureUnivNNReal (canonicalMeasure S K m) : ℝ) ^ (2 : ℝ)⁻¹

theorem n06CanonicalStripL2Cost_nonneg
    (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    0 ≤ n06CanonicalStripL2Cost S K m :=
  Real.rpow_nonneg (NNReal.coe_nonneg _) _

theorem n06CanonicalSmoothJet_norm_le
    {S : PhysicalSpacesData} {K : CanonicalData S} (m j : ℕ)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 j f p| ≤ δ) :
    ‖n05CanonicalSmoothJet S K m hf j‖ ≤ n06CanonicalStripL2Cost S K m * δ := by
  have hae : ∀ᵐ p ∂canonicalMeasure S K m,
      ‖n05CanonicalSmoothJet S K m hf j p‖ ≤ δ := by
    filter_upwards [n05CanonicalSmoothJet_ae S K m hf j,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hstrip
    rw [hp, Real.norm_eq_abs]
    exact hbound p ⟨hstrip.1, mem_univ _⟩
  simpa only [n06CanonicalStripL2Cost, ENNReal.toReal_ofNat] using
    (Lp.norm_le_of_ae_bound hδ hae)

private theorem n06_piL2_norm_le_sum_norm
    {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (v : PiLp 2 E) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  calc
    ‖v‖ = Real.sqrt (∑ i, ‖v i‖ ^ 2) := PiLp.norm_eq_of_L2 v
    _ ≤ Real.sqrt ((∑ i, ‖v i‖) ^ 2) :=
      Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (v i)))
    _ = ∑ i, ‖v i‖ := Real.sqrt_sq (Finset.sum_nonneg (fun i _ => norm_nonneg (v i)))

theorem n06CanonicalSmoothSingleRaw_norm_le
    {S : PhysicalSpacesData} {K : CanonicalData S} (m b : ℕ)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j f p| ≤ δ) :
    ‖n05CanonicalSmoothSingleRaw S K m b hf‖ ≤
      (b + 1 : ℝ) * n06CanonicalStripL2Cost S K m * δ := by
  rw [n05CanonicalSmoothSingleRaw, lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]
  calc
    _ ≤ ∑ j : Fin (b + 1), ‖n05CanonicalSmoothJet S K m hf j.val‖ :=
      n06_piL2_norm_le_sum_norm _
    _ ≤ ∑ _j : Fin (b + 1), n06CanonicalStripL2Cost S K m * δ :=
      Finset.sum_le_sum (fun j _ =>
        n06CanonicalSmoothJet_norm_le m j.val hf hδ (hbound j.val (by omega)))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring

theorem n06CanonicalMaterialWeight_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (γ t : ℝ) (m : ℕ) :
    0 < T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ := by
  have hpos := hT.2.1 _ (spaces_trace_sample_mem hD hT (K.cell m))
  exact mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hpos.2.2.2) _)
    (Real.rpow_pos_of_pos hpos.2.1 _)

section SingleColumn

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}

/-- A genuine smooth source on one cylinder, normalized by the original
forget weight and with every weak angular jet retained. -/
def n06SmoothSourceColumn (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ p : PolarPoint, f (p.1, Real.pi - p.2) = f p) : V.level γ t b :=
  ⟨(T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ)⁻¹ •
      n05CanonicalSmoothSingleRaw S K m b hf, by
    apply (V.level γ t b).smul_mem
    rw [← SetLike.mem_coe, hV.1 γ t b]
    exact n05CanonicalSmoothSingleRaw_mem_graph S K m b hf hp he⟩

theorem n06SmoothSourceColumn_val (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ p : PolarPoint, f (p.1, Real.pi - p.2) = f p) :
    (n06SmoothSourceColumn hV γ t b m hf hp he).val =
      (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ)⁻¹ •
        n05CanonicalSmoothSingleRaw S K m b hf := rfl

theorem n06SmoothSourceColumn_forget (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b m n : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ p : PolarPoint, f (p.1, Real.pi - p.2) = f p)
    (hw : T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ ≠ 0) :
    V.forget γ t b (n06SmoothSourceColumn hV γ t b m hf hp he) n =
      if n = m then n05CanonicalSmoothJet S K n hf 0 else 0 := by
  rw [hV.2.2.2 γ t b, n06SmoothSourceColumn_val]
  by_cases hn : n = m
  · subst n
    simp only [if_pos rfl, lp.coeFn_smul, Pi.smul_apply, PiLp.smul_apply,
      n05CanonicalSmoothSingleRaw_self, Fin.val_zero, smul_smul,
      mul_inv_cancel₀ hw, one_smul, ite_true]
  · simp only [if_neg hn, lp.coeFn_smul, Pi.smul_apply, PiLp.smul_apply,
      n05CanonicalSmoothSingleRaw_ne S K m b hf hn, smul_zero]

theorem n06SmoothSourceColumn_norm_le (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ p : PolarPoint, f (p.1, Real.pi - p.2) = f p)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j f p| ≤ δ) :
    ‖n06SmoothSourceColumn hV γ t b m hf hp he‖ ≤
      (|(T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ)⁻¹| *
        ((b + 1 : ℝ) * n06CanonicalStripL2Cost S K m)) * δ := by
  change ‖(n06SmoothSourceColumn hV γ t b m hf hp he).val‖ ≤ _
  rw [n06SmoothSourceColumn_val, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (n06CanonicalSmoothSingleRaw_norm_le m b hf hδ hbound) (abs_nonneg _)).trans_eq
      (by ring)

end SingleColumn

/-- Explicit finite cost: one inverse material weight and one finite
strip L2 factor per active cylinder, with all orders through b. -/
def n06FiniteSourceCost (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (b : ℕ) (I : Finset ℕ) : ℝ :=
  ∑ m ∈ I,
    |(T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ)⁻¹| *
      ((b + 1 : ℝ) * n06CanonicalStripL2Cost S K m)

theorem n06FiniteSourceCost_nonneg (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (b : ℕ) (I : Finset ℕ) :
    0 ≤ n06FiniteSourceCost T S K γ t b I := by
  apply Finset.sum_nonneg
  intro m _
  exact mul_nonneg (abs_nonneg _)
    (mul_nonneg (by positivity) (n06CanonicalStripL2Cost_nonneg S K m))

/-- Finite smooth even fields with bounded angular jets define an element
of the selected original source level, with its actual physical forget
representatives and a concrete norm bound. -/
theorem n06Volume_exists_finite_smooth_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (b : ℕ)
    (I : Finset ℕ) (f : ℕ → PolarPoint → ℝ)
    (hf : ∀ m, ContDiff ℝ ∞ (f m))
    (hp : ∀ m, Function.Periodic (f m) (0, Real.pi))
    (he : ∀ m p, f m (p.1, Real.pi - p.2) = f m p)
    (hsupport : ∀ m, m ∉ I → f m = 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ m ∈ I, ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j (f m) p| ≤ δ) :
    ∃ F : V.level γ t b,
      (∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f m) ∧
      ‖F‖ ≤ n06FiniteSourceCost T S K γ t b I * δ := by
  classical
  let Y (m : ℕ) : V.level γ t b :=
    n06SmoothSourceColumn hV γ t b m (hf m) (hp m) (he m)
  let F : V.level γ t b := ∑ m ∈ I, Y m
  have hforget (m n : ℕ) : V.forget γ t b (Y m) n =
      if n = m then n05CanonicalSmoothJet S K n (hf m) 0 else 0 :=
    n06SmoothSourceColumn_forget hV γ t b m n (hf m) (hp m) (he m)
      (n06CanonicalMaterialWeight_pos hD hT γ t m).ne'
  refine ⟨F, ?_, ?_⟩
  · intro n
    have hsum : V.forget γ t b F n = ∑ m ∈ I, V.forget γ t b (Y m) n := by
      simp only [F, map_sum, Finset.sum_apply]
    by_cases hn : n ∈ I
    · have heq : V.forget γ t b F n = n05CanonicalSmoothJet S K n (hf n) 0 := by
        rw [hsum, Finset.sum_eq_single n]
        · rw [hforget n n, if_pos rfl]
        · intro m _ hmn
          rw [hforget m n, if_neg (Ne.symm hmn)]
        · exact fun h => False.elim (h hn)
      rw [heq]
      exact n05CanonicalSmoothJet_zero_ae S K n (hf n)
    · have heq : V.forget γ t b F n = 0 := by
        rw [hsum]
        apply Finset.sum_eq_zero
        intro m hm
        exact (hforget m n).trans (if_neg (fun h : n = m => hn (h.symm ▸ hm)))
      rw [heq, hsupport n hn]
      exact Lp.coeFn_zero _ _ _
  · calc
      ‖F‖ ≤ ∑ m ∈ I, ‖Y m‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ I,
          (|(T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ)⁻¹| *
            ((b + 1 : ℝ) * n06CanonicalStripL2Cost S K m)) * δ :=
        Finset.sum_le_sum (fun m hm =>
          n06SmoothSourceColumn_norm_le hV γ t b m (hf m) (hp m) (he m) hδ (hbound m hm))
      _ = n06FiniteSourceCost T S K γ t b I * δ := (Finset.sum_mul I _ δ).symm

end ContinuousFlexibility.Statements
