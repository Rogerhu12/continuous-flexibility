import ContinuousFlexibility.Radial.OscillatorClosedGraph

/-!
# Actual Hilbert-space central inverses on the Hermite graph closure

The multipliers act in genuine Lebesgue L² via the proved coefficient
isometry. The graph relation is proved for the same closed graph defined
as the closure of finite actual Hermite differential pairs. Distribution
and Friedrichs-domain identification are separate subsequent obligations.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private def l2MultiplierLinear (a : ℕ → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) :
    lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2 where
  toFun c := ⟨fun n => a n * c n,
    (lp.memℓp c).norm.const_mul C |>.mono (fun n => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _))⟩
  map_add' c d := by
    ext n
    change a n * (c n + d n) = a n * c n + a n * d n
    ring
  map_smul' r c := by ext n; change a n * (r * c n) = r * (a n * c n); ring

private theorem l2MultiplierLinear_bound (a : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C)
    (c : lp (fun _ : ℕ => ℝ) 2) :
    ‖l2MultiplierLinear a C hC ha c‖ ≤ C * ‖c‖ := by
  calc
    _ ≤ ‖C • c‖ := lp.norm_mono (by norm_num) (fun n => by
      change ‖a n * c n‖ ≤ ‖C * c n‖
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha n) (abs_nonneg _))
    _ = C * ‖c‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

def hermiteBoundedMultiplier {j : ℝ} (hj : 0 < j)
    (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) :
    HermiteL2 →L[ℝ] HermiteL2 :=
  (hermiteCoefficientTransform hj).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((l2MultiplierLinear a C hC ha).mkContinuous C
      (l2MultiplierLinear_bound a C hC ha)).comp
        (hermiteCoefficientTransform hj).toContinuousLinearEquiv.toContinuousLinearMap)

theorem hermiteBoundedMultiplier_coefficient {j : ℝ} (hj : 0 < j)
    (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C)
    (u : HermiteL2) (n : ℕ) :
    hermiteCoefficient j (hermiteBoundedMultiplier hj a C hC ha u) n =
      a n * hermiteCoefficient j u n := by
  rw [← hermiteCoefficientTransform_apply hj, ← hermiteCoefficientTransform_apply hj]
  change (hermiteCoefficientTransform hj)
    ((hermiteCoefficientTransform hj).symm
      (l2MultiplierLinear a C hC ha ((hermiteCoefficientTransform hj) u))) n = _
  rw [(hermiteCoefficientTransform hj).apply_symm_apply]
  rfl

theorem hermiteBoundedMultiplier_bound {j : ℝ} (hj : 0 < j)
    (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C)
    (u : HermiteL2) :
    ‖hermiteBoundedMultiplier hj a C hC ha u‖ ≤ C * ‖u‖ := by
  change ‖(hermiteCoefficientTransform hj).symm
    (l2MultiplierLinear a C hC ha ((hermiteCoefficientTransform hj) u))‖ ≤ _
  rw [(hermiteCoefficientTransform hj).symm.norm_map]
  exact (l2MultiplierLinear_bound a C hC ha _).trans_eq
    (by rw [(hermiteCoefficientTransform hj).norm_map])

theorem hermiteBoundedMultiplier_norm_le {j : ℝ} (hj : 0 < j)
    (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) :
    ‖hermiteBoundedMultiplier hj a C hC ha‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC
    (hermiteBoundedMultiplier_bound hj a C hC ha)

theorem hermiteBoundedMultiplier_vector {j : ℝ} (hj : 0 < j)
    (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) (k : ℕ) :
    hermiteBoundedMultiplier hj a C hC ha (hermiteL2Vector hj k) =
      a k • hermiteL2Vector hj k := by
  apply (hermiteCoefficientTransform hj).injective
  apply lp.ext
  funext m
  rw [hermiteCoefficientTransform_apply, hermiteCoefficientTransform_apply,
    hermiteBoundedMultiplier_coefficient]
  have hr : hermiteCoefficient j (a k • hermiteL2Vector hj k) m =
      a k * hermiteCoefficient j (hermiteL2Vector hj k) m := by
    simpa only [hermiteCoefficientCLM_apply, smul_eq_mul] using
      (hermiteCoefficientCLM hj m).map_smul (a k) (hermiteL2Vector hj k)
  rw [hr, hermiteCoefficient_hermiteL2Vector]
  by_cases hmk : m = k
  · subst m
    rfl
  · simp [hmk]

theorem central_inverse_level_bound (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    |(centralSpectralLevel (2 * (n : ℝ)) m)⁻¹| ≤ 2 / centralGapDelta := by
  have hg := centralSpectralLevel_even_gap n m hn
  have hd : 0 < centralGapDelta / 2 := div_pos centralGapDelta_pos (by norm_num)
  rw [abs_inv]
  have hh := one_div_le_one_div_of_le hd hg
  convert hh using 1 <;> field_simp

private theorem centralEvenFrequency_pos (n : ℕ) (hn : 2 ≤ n) :
    (0 : ℝ) < 2 * (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

def centralHilbertInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  hermiteBoundedMultiplier
    (centralEvenFrequency_pos n hn)
    (fun m => (centralSpectralLevel (2 * (n : ℝ)) m)⁻¹)
    (2 / centralGapDelta) (div_nonneg (by norm_num) centralGapDelta_pos.le)
    (central_inverse_level_bound n hn)

theorem centralHilbertInverse_bound (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    ‖centralHilbertInverse n hn f‖ ≤ (2 / centralGapDelta) * ‖f‖ :=
  hermiteBoundedMultiplier_bound _ _ _ _ _ f

theorem centralHilbertInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralHilbertInverse n hn‖ ≤ 2 / centralGapDelta :=
  hermiteBoundedMultiplier_norm_le _ _ _ _ _

theorem centralHilbertInverse_graph (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    (centralHilbertInverse n hn f, f) ∈
      centralClosedGraph (centralEvenFrequency_pos n hn) := by
  apply (mem_centralClosedGraph_iff _ _ _).mpr
  intro m
  rw [show hermiteCoefficient (2 * (n : ℝ)) (centralHilbertInverse n hn f) m =
      (centralSpectralLevel (2 * (n : ℝ)) m)⁻¹ *
      hermiteCoefficient (2 * (n : ℝ)) f m from
    hermiteBoundedMultiplier_coefficient _ _ _ _ _ f m]
  have he : centralSpectralLevel (2 * (n : ℝ)) m ≠ 0 := by
    have hg := centralSpectralLevel_even_gap n m hn
    intro hz
    rw [hz, abs_zero] at hg
    linarith [centralGapDelta_pos]
  field_simp

theorem centralHilbertInverse_left (n : ℕ) (hn : 2 ≤ n) (u f : HermiteL2)
    (hgraph : (u, f) ∈ centralClosedGraph (centralEvenFrequency_pos n hn)) :
    centralHilbertInverse n hn f = u := by
  have hj : (0 : ℝ) < 2 * (n : ℝ) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  apply (hermiteCoefficientTransform hj).injective
  apply lp.ext
  funext m
  rw [hermiteCoefficientTransform_apply, hermiteCoefficientTransform_apply]
  change hermiteCoefficient (2 * (n : ℝ))
    (hermiteBoundedMultiplier _ _ _ _ _ f) m = _
  rw [hermiteBoundedMultiplier_coefficient, (mem_centralClosedGraph_iff _ _ _).mp hgraph m]
  have he : centralSpectralLevel (2 * (n : ℝ)) m ≠ 0 := by
    have hg := centralSpectralLevel_even_gap n m hn
    intro hz
    rw [hz, abs_zero] at hg
    linarith [centralGapDelta_pos]
  field_simp

/-- Actual unique solvability in the same closed graph for every source. -/
theorem centralClosedGraph_even_exists_unique (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    ∃! u : HermiteL2, (u, f) ∈ centralClosedGraph (centralEvenFrequency_pos n hn) := by
  refine ⟨centralHilbertInverse n hn f, centralHilbertInverse_graph n hn f, ?_⟩
  intro u hu
  exact (centralHilbertInverse_left n hn u f hu).symm

theorem reduced_inverse_level_bound (m : ℕ) :
    |(4 * (m : ℝ))⁻¹| ≤ (1 / 4 : ℝ) := by
  by_cases hm : m = 0
  · subst m; norm_num
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    rw [abs_inv, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * m)]
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ 4 * (m : ℝ))

def centralReducedHilbertInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  hermiteBoundedMultiplier (by norm_num : (0 : ℝ) < 2)
    (fun m => (4 * (m : ℝ))⁻¹) (1 / 4) (by norm_num) reduced_inverse_level_bound

theorem centralReducedHilbertInverse_bound (f : HermiteL2) :
    ‖centralReducedHilbertInverse f‖ ≤ (1 / 4 : ℝ) * ‖f‖ :=
  hermiteBoundedMultiplier_bound _ _ _ _ _ f

theorem centralReducedHilbertInverse_norm_le :
    ‖centralReducedHilbertInverse‖ ≤ (1 / 4 : ℝ) :=
  hermiteBoundedMultiplier_norm_le _ _ _ _ _

/-- The bound on the reduced inverse is sharp, witnessed by the first
excited actual Hermite function. -/
theorem centralReducedHilbertInverse_norm :
    ‖centralReducedHilbertInverse‖ = (1 / 4 : ℝ) := by
  have hvec : centralReducedHilbertInverse
      (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 1) =
      (1 / 4 : ℝ) • hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 1 := by
    simpa only [centralReducedHilbertInverse, Nat.cast_one, mul_one, one_div] using
      hermiteBoundedMultiplier_vector (by norm_num : (0 : ℝ) < 2)
        (fun m => (4 * (m : ℝ))⁻¹) (1 / 4) (by norm_num) reduced_inverse_level_bound 1
  have hv := (hermiteL2Vector_orthonormal (by norm_num : (0 : ℝ) < 2)).norm_eq_one 1
  have hle := centralReducedHilbertInverse.le_opNorm
    (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 1)
  rw [hvec, norm_smul, hv] at hle
  norm_num at hle
  exact le_antisymm centralReducedHilbertInverse_norm_le hle

theorem centralReducedHilbertInverse_zero_coefficient (f : HermiteL2) :
    hermiteCoefficient 2 (centralReducedHilbertInverse f) 0 = 0 := by
  change hermiteCoefficient 2
    (hermiteBoundedMultiplier _ _ _ _ _ f) 0 = 0
  rw [hermiteBoundedMultiplier_coefficient]
  norm_num

theorem centralReducedHilbertInverse_graph (f : HermiteL2)
    (hf : hermiteCoefficient 2 f 0 = 0) :
    (centralReducedHilbertInverse f, f) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
  apply (mem_centralClosedGraph_iff _ _ _).mpr
  intro m
  change hermiteCoefficient 2 f m =
    centralSpectralLevel 2 m *
      hermiteCoefficient 2 (hermiteBoundedMultiplier _ _ _ _ _ f) m
  rw [centralSpectralLevel_two, hermiteBoundedMultiplier_coefficient]
  by_cases hm : m = 0
  · subst m; simp [hf]
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp

theorem centralReducedHilbertInverse_left (u f : HermiteL2)
    (hgraph : (u, f) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2))
    (hu : hermiteCoefficient 2 u 0 = 0) :
    centralReducedHilbertInverse f = u := by
  apply (hermiteCoefficientTransform (by norm_num : (0 : ℝ) < 2)).injective
  apply lp.ext
  funext m
  rw [hermiteCoefficientTransform_apply, hermiteCoefficientTransform_apply]
  change hermiteCoefficient 2
    (hermiteBoundedMultiplier _ _ _ _ _ f) m = _
  rw [hermiteBoundedMultiplier_coefficient,
    (mem_centralClosedGraph_iff _ _ _).mp hgraph m, centralSpectralLevel_two]
  by_cases hm : m = 0
  · subst m; simp [hu]
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp

/-- The actual ground-state pairing is the necessary source obstruction. -/
theorem centralClosedGraph_two_source_compatible (u f : HermiteL2)
    (hgraph : (u, f) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2)) :
    hermiteCoefficient 2 f 0 = 0 := by
  have h := (mem_centralClosedGraph_iff _ _ _).mp hgraph 0
  rw [centralSpectralLevel_two] at h
  simpa only [Nat.cast_zero, mul_zero, zero_mul] using h

/-- Exactly the compatible sources admit a unique ground-normalized
solution in the same closed differential-core graph. -/
theorem centralClosedGraph_two_exists_unique_iff (f : HermiteL2) :
    (∃! u : HermiteL2,
      (u, f) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2) ∧
        hermiteCoefficient 2 u 0 = 0) ↔
      hermiteCoefficient 2 f 0 = 0 := by
  constructor
  · rintro ⟨u, hu, _⟩
    exact centralClosedGraph_two_source_compatible u f hu.1
  · intro hf
    refine ⟨centralReducedHilbertInverse f,
      ⟨centralReducedHilbertInverse_graph f hf,
        centralReducedHilbertInverse_zero_coefficient f⟩, ?_⟩
    intro u hu
    exact (centralReducedHilbertInverse_left u f hu.1 hu.2).symm

/-- The actual rank-one orthogonal projection onto the normalized Gaussian. -/
def centralGroundProjection : HermiteL2 →L[ℝ] HermiteL2 :=
  (hermiteCoefficientCLM (by norm_num : (0 : ℝ) < 2) 0).smulRight
    (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0)

theorem centralGroundProjection_apply (f : HermiteL2) :
    centralGroundProjection f = hermiteCoefficient 2 f 0 •
      hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0 := by
  simp only [centralGroundProjection, ContinuousLinearMap.smulRight_apply,
    hermiteCoefficientCLM_apply]

theorem centralGroundProjection_coefficient (f : HermiteL2) (m : ℕ) :
    hermiteCoefficient 2 (centralGroundProjection f) m =
      if m = 0 then hermiteCoefficient 2 f 0 else 0 := by
  rw [centralGroundProjection_apply]
  have hr := (hermiteCoefficientCLM (by norm_num : (0 : ℝ) < 2) m).map_smul
    (hermiteCoefficient 2 f 0) (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0)
  rw [hermiteCoefficientCLM_apply, hermiteCoefficientCLM_apply,
    hermiteCoefficient_hermiteL2Vector] at hr
  simpa only [smul_eq_mul, mul_ite, mul_one, mul_zero] using hr

theorem centralGroundProjection_idempotent (f : HermiteL2) :
    centralGroundProjection (centralGroundProjection f) = centralGroundProjection f := by
  rw [centralGroundProjection_apply, centralGroundProjection_coefficient]
  simp only [ite_true, centralGroundProjection_apply]

theorem centralGroundProjection_orthogonal (f : HermiteL2) :
    ⟪f - centralGroundProjection f,
      hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0⟫_ℝ = 0 := by
  rw [centralGroundProjection_apply, inner_sub_left, real_inner_smul_left,
    inner_hermiteL2Vector_right, hermiteL2Vector_inner]
  simp

/-- The reduced inverse solves the source with its genuine ground-state
projection removed, for arbitrary actual L² data. -/
theorem centralReducedHilbertInverse_graph_projected (f : HermiteL2) :
    (centralReducedHilbertInverse f, f - centralGroundProjection f) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
  apply (mem_centralClosedGraph_iff _ _ _).mpr
  intro m
  have hr := (hermiteCoefficientCLM (by norm_num : (0 : ℝ) < 2) m).map_sub
    f (centralGroundProjection f)
  simp only [hermiteCoefficientCLM_apply] at hr
  rw [hr, centralGroundProjection_coefficient, centralSpectralLevel_two]
  change hermiteCoefficient 2 f m - (if m = 0 then hermiteCoefficient 2 f 0 else 0) =
    4 * (m : ℝ) * hermiteCoefficient 2 (hermiteBoundedMultiplier _ _ _ _ _ f) m
  rw [hermiteBoundedMultiplier_coefficient]
  by_cases hm : m = 0
  · subst m
    simp
  · simp only [ite_eq_right hm, sub_zero]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp

/-- The opposite reduced inverse identity on the same graph. -/
theorem centralReducedHilbertInverse_left_projected (u f : HermiteL2)
    (hgraph : (u, f) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2)) :
    centralReducedHilbertInverse f = u - centralGroundProjection u := by
  apply (hermiteCoefficientTransform (by norm_num : (0 : ℝ) < 2)).injective
  apply lp.ext
  funext m
  rw [hermiteCoefficientTransform_apply, hermiteCoefficientTransform_apply]
  have hr := (hermiteCoefficientCLM (by norm_num : (0 : ℝ) < 2) m).map_sub
    u (centralGroundProjection u)
  simp only [hermiteCoefficientCLM_apply] at hr
  rw [hr, centralGroundProjection_coefficient]
  change hermiteCoefficient 2 (hermiteBoundedMultiplier _ _ _ _ _ f) m = _
  rw [hermiteBoundedMultiplier_coefficient,
    (mem_centralClosedGraph_iff _ _ _).mp hgraph m, centralSpectralLevel_two]
  by_cases hm : m = 0
  · subst m
    simp
  · simp only [ite_eq_right hm, sub_zero]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp

end ContinuousFlexibility.Radial

