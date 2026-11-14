module

public import ContinuousFlexibility.Radial.TailFiniteLowHats
public import ContinuousFlexibility.Radial.TailMassCells
public import ContinuousFlexibility.Radial.TailReflectedInverse

/-!
# Normalized low-mode synthesis in the actual closed form

The index is the set of active mass cells whose complete hat fits before
the given wall. Every normalized hat is an actual compact smooth core
element. The finite estimates construct its bounded synthesis in the
closed Friedrichs form space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff lp ENNReal InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

abbrev TailLowIndex (T : DeepTailData) (cut : ℝ) : Type :=
  {n : ℕ // tailFirstMassIndex T ≤ n ∧ T.node (n + 1) ≤ cut}

theorem tailHat_memLp (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    MemLp (tailLowHat T hT n) 2 (deepTailMeasure T) :=
  tail_test_memLp ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
    (fun x hx => deepTail_pos hT x (Ioo_subset_Ico_self hx))
    (tailLowHat_smooth T hT n) (tailLowHat_compact T hT n) (tailLowHat_support T hT n)

theorem tailHatDerivative_memLp (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    MemLp (deriv (tailLowHat T hT n)) 2 (deepTailMeasure T) :=
  tail_test_memLp ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
    (fun x hx => deepTail_pos hT x (Ioo_subset_Ico_self hx))
    (contDiff_infty_iff_deriv.mp (tailLowHat_smooth T hT n)).2
    (tailLowHat_compact T hT n).deriv
    (tsupport_deriv_subset.trans (tailLowHat_support T hT n))

def tailHatL2 (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : DeepTailL2 T :=
  (tailHat_memLp T hT n).toLp (tailLowHat T hT n)

def tailHatDerivativeL2 (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : DeepTailL2 T :=
  (tailHatDerivative_memLp T hT n).toLp (deriv (tailLowHat T hT n))

theorem tailHatL2_coeFn (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    (tailHatL2 T hT n : ℝ → ℝ) =ᵐ[deepTailMeasure T] tailLowHat T hT n :=
  MemLp.coeFn_toLp _

theorem tailHatDerivativeL2_coeFn (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    (tailHatDerivativeL2 T hT n : ℝ → ℝ) =ᵐ[deepTailMeasure T] deriv (tailLowHat T hT n) :=
  MemLp.coeFn_toLp _

def tailNormalizedHatPair (T : DeepTailData) (hT : DeepTailHypotheses T)
    (n : ℕ) : DeepTailL2 T × DeepTailL2 T :=
  ((Real.sqrt (tailMass T n))⁻¹ • tailHatL2 T hT n,
    (Real.sqrt (tailMass T n))⁻¹ • tailHatDerivativeL2 T hT n)

theorem tailNormalizedHatPair_core (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (i : TailLowIndex T cut) : tailNormalizedHatPair T hT i ∈ TailEnergyCore T cut := by
  refine ⟨fun x => (Real.sqrt (tailMass T i))⁻¹ * tailLowHat T hT i x,
    contDiff_const.mul (tailLowHat_smooth T hT i), (tailLowHat_compact T hT i).mul_left, ?_, ?_, ?_⟩
  · exact tsupport_mul_subset_right.trans
      ((tailLowHat_support_truncation T hT i).trans
        (fun x hx => ⟨hx.1, hx.2.trans_le i.property.2⟩))
  · filter_upwards [Lp.coeFn_smul (Real.sqrt (tailMass T i))⁻¹ (tailHatL2 T hT i),
      tailHatL2_coeFn T hT i] with x hx hhat
    simpa only [tailNormalizedHatPair, Pi.smul_apply, smul_eq_mul, hhat] using hx
  · filter_upwards [Lp.coeFn_smul (Real.sqrt (tailMass T i))⁻¹ (tailHatDerivativeL2 T hT i),
      tailHatDerivativeL2_coeFn T hT i] with x hx hhat
    simpa only [tailNormalizedHatPair, Pi.smul_apply, smul_eq_mul, hhat,
      deriv_const_mul_field] using hx

def tailNormalizedHat (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (i : TailLowIndex T cut) : tailGradientSpace T cut :=
  ⟨WithLp.toLp 2 (tailNormalizedHatPair T hT i),
    (mem_tailGradientSpace T cut _).mpr (by
      rw [WithLp.ofLp_toLp]
      exact subset_closure (tailNormalizedHatPair_core T hT cut i))⟩

theorem tailNormalizedHat_core (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (i : TailLowIndex T cut) :
    WithLp.ofLp (tailNormalizedHat T hT cut i : GradientHilbert (DeepTailL2 T)) ∈
      TailEnergyCore T cut := by
  simpa only [tailNormalizedHat, WithLp.ofLp_toLp] using tailNormalizedHatPair_core T hT cut i

theorem tailNormalizedHat_base (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (i : TailLowIndex T cut) :
    tailFormBase T cut (tailNormalizedHat T hT cut i) =
      (Real.sqrt (tailMass T i))⁻¹ • tailHatL2 T hT i := by
  simp only [tailFormBase_apply, tailNormalizedHat, WithLp.toLp_fst, tailNormalizedHatPair]

theorem tailNormalizedHat_gradient (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (i : TailLowIndex T cut) :
    tailFormGradient T cut (tailNormalizedHat T hT cut i) =
      (Real.sqrt (tailMass T i))⁻¹ • tailHatDerivativeL2 T hT i := by
  simp only [tailFormGradient_apply, tailNormalizedHat, WithLp.toLp_snd, tailNormalizedHatPair]

theorem tailNormalizedHat_base_coeFn (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (i : TailLowIndex T cut) :
    (tailFormBase T cut (tailNormalizedHat T hT cut i) : ℝ → ℝ) =ᵐ[deepTailMeasure T]
      fun x => (Real.sqrt (tailMass T i))⁻¹ * tailLowHat T hT i x := by
  rw [tailNormalizedHat_base]
  filter_upwards [Lp.coeFn_smul (Real.sqrt (tailMass T i))⁻¹ (tailHatL2 T hT i),
    tailHatL2_coeFn T hT i] with x hx hhat
  simpa only [Pi.smul_apply, smul_eq_mul, hhat] using hx

theorem tailNormalizedHat_gradient_coeFn (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (i : TailLowIndex T cut) :
    (tailFormGradient T cut (tailNormalizedHat T hT cut i) : ℝ → ℝ) =ᵐ[deepTailMeasure T]
      fun x => (Real.sqrt (tailMass T i))⁻¹ * deriv (tailLowHat T hT i) x := by
  rw [tailNormalizedHat_gradient]
  filter_upwards [Lp.coeFn_smul (Real.sqrt (tailMass T i))⁻¹ (tailHatDerivativeL2 T hT i),
    tailHatDerivativeL2_coeFn T hT i] with x hx hhat
  simpa only [Pi.smul_apply, smul_eq_mul, hhat] using hx

/-- Normalized subtype coefficients, extended by zero to all mass indices. -/
def tailLowCoefficients (T : DeepTailData) (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) : ℕ →₀ ℝ :=
  (Finsupp.onFinset a.support (fun i => a i * (Real.sqrt (tailMass T i))⁻¹)
    (fun i hi => Finsupp.mem_support_iff.mpr (fun hz => hi (by simp only [hz, zero_mul])))).embDomain
      ⟨Subtype.val, Subtype.val_injective⟩

theorem tailLowCoefficients_apply (T : DeepTailData) (cut : ℝ)
    (a : TailLowIndex T cut →₀ ℝ) (i : TailLowIndex T cut) :
    tailLowCoefficients T cut a i = a i * (Real.sqrt (tailMass T i))⁻¹ := by
  have h := Finsupp.embDomain_apply_self
    (⟨Subtype.val, Subtype.val_injective⟩ : TailLowIndex T cut ↪ ℕ)
    (Finsupp.onFinset a.support (fun j => a j * (Real.sqrt (tailMass T j))⁻¹)
      (fun j hj => Finsupp.mem_support_iff.mpr
        (fun hz => hj (by simp only [hz, zero_mul])))) i
  simpa only [tailLowCoefficients, Function.Embedding.coeFn_mk,
    Finsupp.onFinset_apply] using h

theorem tailLowCoefficients_active (T : DeepTailData) (cut : ℝ)
    (a : TailLowIndex T cut →₀ ℝ) :
    ∀ n ∈ (tailLowCoefficients T cut a).support, tailFirstMassIndex T ≤ n := by
  intro n hn
  rw [tailLowCoefficients, Finsupp.support_embDomain] at hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hn
  exact i.property.1

theorem tailLowCoefficients_cut (T : DeepTailData) (cut : ℝ)
    (a : TailLowIndex T cut →₀ ℝ) :
    ∀ n ∈ (tailLowCoefficients T cut a).support, T.node (n + 1) ≤ cut := by
  intro n hn
  rw [tailLowCoefficients, Finsupp.support_embDomain] at hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hn
  exact i.property.2

theorem tailLowCoefficients_linearCombination {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : DeepTailData) (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) (v : ℕ → E) :
    Finsupp.linearCombination ℝ v (tailLowCoefficients T cut a) =
      ∑ i ∈ a.support, (a i * (Real.sqrt (tailMass T i))⁻¹) • v i := by
  rw [Finsupp.linearCombination_apply, tailLowCoefficients, Finsupp.sum_embDomain,
    Finsupp.sum_onFinset]
  · simp only [Function.Embedding.coeFn_mk]
  · intro i _
    exact zero_smul ℝ (v i)

theorem tailLowCoefficients_mass (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) :
    tailCoefficientMass T (tailLowCoefficients T cut a) = ‖tailFiniteEmbedding a‖ ^ 2 := by
  have hsum := Finsupp.sum_of_support_subset (tailLowCoefficients T cut a)
    (Finset.Subset.refl _) (fun n r => tailMass T n * r ^ 2)
    (by intro n _; simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero])
  rw [tailCoefficientMass, ← hsum, tailLowCoefficients, Finsupp.sum_embDomain,
    Finsupp.sum_onFinset, tailFiniteEmbedding_norm_sq]
  · apply Finset.sum_congr rfl
    intro i _
    try dsimp only
    simp only [Function.Embedding.coeFn_mk]
    rw [Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, Real.sq_sqrt (tailMass_pos hT i).le]
    field_simp [(tailMass_pos hT i).ne'] <;> ring
  · intro i _
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]

theorem tailHatL2_finite_coeFn (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) :
    (Finsupp.linearCombination ℝ (tailHatL2 T hT) a : ℝ → ℝ) =ᵐ[deepTailMeasure T]
      tailFiniteLowHat T hT a := by
  apply (Lp.coeFn_linearCombination a (tailHatL2 T hT)).trans
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (Finsupp.mem_supported_support ℝ a)]
  filter_upwards [ae_all_iff.mpr (fun n => tailHatL2_coeFn T hT n)] with x hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tailFiniteLowHat]
  exact Finset.sum_congr rfl (fun n _ => congrArg (a n * ·) (hx n))

theorem tailHatDerivativeL2_finite_coeFn (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) :
    (Finsupp.linearCombination ℝ (tailHatDerivativeL2 T hT) a : ℝ → ℝ) =ᵐ[deepTailMeasure T]
      deriv (tailFiniteLowHat T hT a) := by
  apply (Lp.coeFn_linearCombination a (tailHatDerivativeL2 T hT)).trans
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (Finsupp.mem_supported_support ℝ a)]
  filter_upwards [ae_all_iff.mpr (fun n => tailHatDerivativeL2_coeFn T hT n)] with x hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tailFiniteLowHat_deriv]
  exact Finset.sum_congr rfl (fun n _ => congrArg (a n * ·) (hx n))

theorem tailNormalizedHat_finite_base (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) :
    tailFormBase T cut (Finsupp.linearCombination ℝ (tailNormalizedHat T hT cut) a) =
      Finsupp.linearCombination ℝ (tailHatL2 T hT) (tailLowCoefficients T cut a) := by
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (Finsupp.mem_supported_support ℝ a),
    map_sum, tailLowCoefficients_linearCombination]
  simp only [map_smul, tailNormalizedHat_base, smul_smul]

theorem tailNormalizedHat_finite_gradient (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) :
    tailFormGradient T cut (Finsupp.linearCombination ℝ (tailNormalizedHat T hT cut) a) =
      Finsupp.linearCombination ℝ (tailHatDerivativeL2 T hT) (tailLowCoefficients T cut a) := by
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (Finsupp.mem_supported_support ℝ a),
    map_sum, tailLowCoefficients_linearCombination]
  simp only [map_smul, tailNormalizedHat_gradient, smul_smul]

theorem tailNormalizedHat_finite_core (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) :
    (tailFormBase T cut (Finsupp.linearCombination ℝ (tailNormalizedHat T hT cut) a),
      tailFormGradient T cut (Finsupp.linearCombination ℝ (tailNormalizedHat T hT cut) a)) ∈
      TailEnergyCore T cut := by
  let L := (tailFormBase T cut).prod (tailFormGradient T cut)
  have hL (u : tailGradientSpace T cut) : L u =
      (tailFormBase T cut u, tailFormGradient T cut u) :=
    ContinuousLinearMap.prod_apply _ _ _
  apply (mem_tailEnergyCoreSubmodule T cut _).mp
  rw [← hL, Finsupp.linearCombination_apply_of_mem_supported ℝ
    (Finsupp.mem_supported_support ℝ a), map_sum]
  apply (tailEnergyCoreSubmodule T cut).sum_mem
  intro i _
  rw [map_smul]
  apply (tailEnergyCoreSubmodule T cut).smul_mem
  apply (mem_tailEnergyCoreSubmodule T cut _).mpr
  rw [hL, tailNormalizedHat_base, tailNormalizedHat_gradient]
  exact tailNormalizedHatPair_core T hT cut i

def tailLowEnergyCoefficient (T : DeepTailData) : ℝ :=
  5 * tailSmoothStepConstant * T.Λ / T.K

theorem tailLowEnergyCoefficient_nonneg (T : DeepTailData) (hT : DeepTailHypotheses T) :
    0 ≤ tailLowEnergyCoefficient T :=
  div_nonneg (mul_nonneg (mul_nonneg (by norm_num) tailSmoothStepConstant_pos.le) hT.2.2.1.le)
    (lt_trans zero_lt_one hT.2.2.2.2.2.2.1).le

def tailLowSynthesisNormBound (T : DeepTailData) : ℝ :=
  Real.sqrt (1 + 5 * T.η + tailLowEnergyCoefficient T)

theorem tailNormalizedHat_finite_gradient_sq (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) :
    ‖tailFormGradient T cut (Finsupp.linearCombination ℝ (tailNormalizedHat T hT cut) a)‖ ^ 2 ≤
      tailLowEnergyCoefficient T * ‖tailFiniteEmbedding a‖ ^ 2 := by
  rw [tailNormalizedHat_finite_gradient,
    tail_norm_sq_of_ae _ (tailHatDerivativeL2_finite_coeFn T hT (tailLowCoefficients T cut a))]
  have h := (tailFiniteLowHat_bounds T hT (tailLowCoefficients T cut a)
    (tailLowCoefficients_active T cut a)).2.2
  rw [tailLowCoefficients_mass T hT cut a] at h
  exact h

theorem tailNormalizedHat_finite_base_sq (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) :
    ‖tailFormBase T cut (Finsupp.linearCombination ℝ (tailNormalizedHat T hT cut) a)‖ ^ 2 ≤
      (1 + 5 * T.η) * ‖tailFiniteEmbedding a‖ ^ 2 := by
  rw [tailNormalizedHat_finite_base,
    tail_norm_sq_of_ae _ (tailHatL2_finite_coeFn T hT (tailLowCoefficients T cut a))]
  have h := (tailFiniteLowHat_bounds T hT (tailLowCoefficients T cut a)
    (tailLowCoefficients_active T cut a)).2.1
  rwa [tailLowCoefficients_mass T hT cut a] at h

theorem tailNormalizedHat_finite_bound (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (a : TailLowIndex T cut →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ (tailNormalizedHat T hT cut) a‖ ≤
      tailLowSynthesisNormBound T * ‖tailFiniteEmbedding a‖ := by
  unfold tailLowSynthesisNormBound
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,
    Real.sq_sqrt (by have := tailLowEnergyCoefficient_nonneg T hT; have := hT.2.2.2.2.1; positivity),
    tailForm_norm_sq]
  have hb := tailNormalizedHat_finite_base_sq T hT cut a
  have hg := tailNormalizedHat_finite_gradient_sq T hT cut a
  nlinarith

theorem tailLowIndex_mass_disjoint (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) :
    Pairwise (fun i j : TailLowIndex T cut => Disjoint (tailMassCell T i) (tailMassCell T j)) := by
  intro i j hij
  exact tailMassCell_pairwiseDisjoint hT (fun h => hij (Subtype.ext h))

def tailLowAnalysis (T : DeepTailData) (hT : DeepTailHypotheses T) (cut : ℝ) :
    DeepTailL2 T →L[ℝ] ℓ²(TailLowIndex T cut, ℝ) :=
  tailMassAnalysis (fun i : TailLowIndex T cut => tailMassCell T i)
    (fun i => tailMassCell_measurable T i) (fun i => tailMassCell_measure_ne_top hT i)
    (fun i => tailMassCell_real_pos hT i) (tailLowIndex_mass_disjoint T hT cut)

theorem tailLowAnalysis_apply (T : DeepTailData) (hT : DeepTailHypotheses T) (cut : ℝ)
    (u : DeepTailL2 T) (i : TailLowIndex T cut) :
    tailLowAnalysis T hT cut u i = (Real.sqrt (tailMass T i))⁻¹ *
      ∫ x in tailMassCell T i, u x ∂deepTailMeasure T := by
  rw [tailLowAnalysis, tailMassAnalysis_apply, tailMassCell_real hT]

theorem norm_tailLowAnalysis_le (T : DeepTailData) (hT : DeepTailHypotheses T) (cut : ℝ) :
    ‖tailLowAnalysis T hT cut‖ ≤ 1 :=
  norm_tailMassAnalysis_le _ _ _ _ _

theorem tailNormalizedHat_analysis (T : DeepTailData) (hT : DeepTailHypotheses T)
    (cut : ℝ) (j : TailLowIndex T cut) :
    tailLowAnalysis T hT cut (tailFormBase T cut (tailNormalizedHat T hT cut j)) =
      lp.single 2 j (1 : ℝ) := by
  apply lp.ext
  funext i
  rw [tailLowAnalysis_apply, lp.single_apply]
  have hint : (∫ x in tailMassCell T i,
      tailFormBase T cut (tailNormalizedHat T hT cut j) x ∂deepTailMeasure T) =
      tailMass T i * ((Real.sqrt (tailMass T j))⁻¹ *
        (if (j : ℕ) = (i : ℕ) then 1 else 0)) := by
    calc
      _ = ∫ _ in tailMassCell T i, (Real.sqrt (tailMass T j))⁻¹ *
          (if (j : ℕ) = (i : ℕ) then 1 else 0) ∂deepTailMeasure T := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (tailNormalizedHat_base_coeFn T hT cut j),
          ae_restrict_mem (tailMassCell_measurable T i)] with x hx hxi
        try dsimp only
        rw [hx, tailLowHat_mass T hT j j.property.1 i ⟨hxi.1.le, hxi.2.le⟩]
      _ = _ := by rw [setIntegral_const, smul_eq_mul, tailMassCell_real hT]
  rw [hint]
  by_cases hij : i = j
  · subst j
    simp only [eq_self_iff_true, ite_true, mul_one, Pi.single_eq_same]
    have hr : Real.sqrt (tailMass T i) ≠ 0 := (Real.sqrt_pos.mpr (tailMass_pos hT i)).ne'
    field_simp [hr]
    nlinarith [Real.sq_sqrt (tailMass_pos hT i).le]
  · have hji : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Subtype.ext h.symm)
    simp only [if_neg hji, mul_zero, Pi.single_eq_of_ne hij]

end ContinuousFlexibility.Radial
