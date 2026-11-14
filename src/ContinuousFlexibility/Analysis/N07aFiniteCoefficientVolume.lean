module

public import ContinuousFlexibility.Analysis.N07aCanonicalJetNormBounds

/-!
# Actual weighted realization of finitely supported coefficient columns

All jets vanish on pieces where the original open coefficient vanishes.
The resulting finite sequence lies in every material level, with the
literal finite sum of the original jet norms as its bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped BigOperators ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

theorem N07aCanonicalOpenCoefficient.jet_toLp_eq_zero_of_eqOn {m : ℕ}
    (χ : N07aCanonicalOpenCoefficient S K m)
    (hzero : EqOn χ.value (fun _ => (0 : ℝ)) (canonicalOpen S K m)) (a b : ℕ) :
    (χ.jet a b).toLp = 0 := by
  apply Lp.ext
  filter_upwards [(χ.jet a b).toLp_ae,
    n07a_canonicalOpen_ae (S := S) (K := K) (m := m),
    Lp.coeFn_zero ℝ 2 (canonicalMeasure S K m)] with p hp hpU hp0
  have hd := n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ) hzero a b hpU
  have hz : mixedDerivative a b χ.value p = 0 := by
    simpa only [mixedDerivative, iteratedDeriv_fun_const_zero] using hd
  exact hp.trans (hz.trans hp0.symm)

theorem n07a_lp_finite_norm_le
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (v : lp E 2) (I : Finset ι) (hzero : ∀ i, i ∉ I → v i = 0) :
    ‖v‖ ≤ ∑ i ∈ I, ‖v i‖ := by
  classical
  have he : v = ∑ i ∈ I, lp.single 2 i (v i) := by
    ext i
    by_cases hi : i ∈ I
    · simp only [lp.coeFn_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · exact (lp.single_apply_self _ _ _).symm
      · intro j _ hji
        exact lp.single_apply_ne (E := E) 2 j (v j) hji.symm
      · exact fun h => (h hi).elim
    · simp only [lp.coeFn_sum, Finset.sum_apply]
      rw [hzero i hi]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      exact lp.single_apply_ne (E := E) 2 j (v j) (fun h => hi (h.symm ▸ hj))
  calc
    ‖v‖ = ‖∑ i ∈ I, lp.single 2 i (v i)‖ := congrArg norm he
    _ ≤ ∑ i ∈ I, ‖lp.single 2 i (v i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ I, ‖v i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      exact lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2) i (v i)

local instance n07aFiniteCoefficientLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aFiniteCoefficientLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem exists_n07aFiniteCoefficientVolume
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (χ : ∀ m, N07aCanonicalOpenCoefficient S K m)
    (heven : ∀ m p, p ∈ canonicalOpen S K m → (χ m).value (p.1, -p.2) = (χ m).value p)
    (I : Finset ℕ)
    (hzero : ∀ m, m ∉ I → EqOn (χ m).value (fun _ => (0 : ℝ)) (canonicalOpen S K m)) :
    ∃ W : V.level γ t s, V.forget γ t s W = (fun m => (χ m).toLp) ∧
      ‖W‖ ≤ ∑ m ∈ I, (n07aVolumeWeight T K γ t m)⁻¹ *
        ∑ j : Fin (s + 1), ‖((χ m).jet 0 j.val).toLp‖ := by
  classical
  let a : ℕ → ℝ := fun m => (n07aVolumeWeight T K γ t m)⁻¹
  let v := n07aCanonicalCoefficientJetArray χ s a
  have hvzero (m : ℕ) (hm : m ∉ I) : v m = 0 := by
    ext j
    rw [n07aCanonicalCoefficientJetArray_apply,
      (χ m).jet_toLp_eq_zero_of_eqOn (hzero m hm), smul_zero, PiLp.zero_apply]
  have hmem : Memℓp v 2 := by
    apply memℓp_gen
    apply summable_of_ne_finset_zero (s := I)
    intro m hm
    rw [hvzero m hm, norm_zero]
    norm_num
  let W := n07aOpenCoefficientVolume hV γ t s χ heven hmem
  refine ⟨W, n07aOpenCoefficientVolume_forget hD hT hV γ t s χ heven hmem, ?_⟩
  have hnorm : ‖W‖ ≤ ∑ m ∈ I, ‖v m‖ :=
    n07a_lp_finite_norm_le (⟨v, hmem⟩ : CanonicalVolumeJets S K s) I hvzero
  apply hnorm.trans
  apply Finset.sum_le_sum
  intro m hm
  have ha : 0 < a m := inv_pos.mpr (n07aVolumeWeight_pos hD hT γ t m)
  calc
    ‖v m‖ ≤ ∑ j : Fin (s + 1), ‖v m j‖ := n07a_piLp_two_norm_le_sum_norm _
    _ = a m * ∑ j : Fin (s + 1), ‖((χ m).jet 0 j.val).toLp‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [n07aCanonicalCoefficientJetArray_apply, norm_smul, Real.norm_eq_abs, abs_of_pos ha]

end ContinuousFlexibility.Analysis
