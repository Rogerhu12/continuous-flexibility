import ContinuousFlexibility.Analysis.ReferenceAffineCutoffNormalTest
import ContinuousFlexibility.Analysis.OpticalCollarCutoff
import ContinuousFlexibility.Analysis.N08EndpointDistanceEnvelope
import ContinuousFlexibility.Analysis.MaterialCellHeightTransport

/-!
# Actual root-centred compact tests with a fixed material cutoff cost

Two fixed transitions give a plateau on the inner half of a physical
collar.  Its radius is half the actual ambient endpoint distance, without
using a turning-slope lower bound or selecting a new reference witness.
The all-order cutoff constants are chosen before the physical centre.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def referenceCenteredCutoff (c δ : ℝ) (r : ℝ) : ℝ :=
  returnOpticalCutoff (c - 3 * δ / 4) (δ / 4) r -
    returnOpticalCutoff (c + 3 * δ / 4) (δ / 4) r

theorem referenceCenteredCutoff_contDiff (c δ : ℝ) :
    ContDiff ℝ ∞ (referenceCenteredCutoff c δ) :=
  (returnOpticalCutoff_contDiff _ _).sub (returnOpticalCutoff_contDiff _ _)

theorem referenceCenteredCutoff_abs_le_one (c δ r : ℝ) :
    |referenceCenteredCutoff c δ r| ≤ 1 := by
  have hl := returnOpticalCutoff_mem_Icc (c - 3 * δ / 4) (δ / 4) r
  have hr := returnOpticalCutoff_mem_Icc (c + 3 * δ / 4) (δ / 4) r
  unfold referenceCenteredCutoff
  exact abs_le.mpr ⟨by linarith only [hl.1, hr.2], by linarith only [hl.2, hr.1]⟩

theorem referenceCenteredCutoff_one_germ (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    referenceCenteredCutoff c δ =ᶠ[𝓝 c] fun _ => 1 := by
  have hl := returnOpticalCutoff_eventually_one (x := c - 3 * δ / 4)
    (δ := δ / 4) (r := c) (by linarith) (by linarith)
  have hr := returnOpticalCutoff_eventually_zero (x := c + 3 * δ / 4)
    (δ := δ / 4) (r := c) (by linarith) (by linarith)
  filter_upwards [hl, hr] with r hl hr
  simp only [referenceCenteredCutoff, hl, hr, sub_zero]

theorem referenceCenteredCutoff_tsupport (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    tsupport (referenceCenteredCutoff c δ) ⊆ Icc (c - δ) (c + δ) := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  by_contra hnot
  by_cases hleft : r < c - δ
  · have hl := returnOpticalCutoff_eventually_zero (x := c - 3 * δ / 4)
      (δ := δ / 4) (r := r) (by linarith) (by linarith)
    have hh := returnOpticalCutoff_eventually_zero (x := c + 3 * δ / 4)
      (δ := δ / 4) (r := r) (by linarith) (by linarith)
    exact hr (by simp only [referenceCenteredCutoff, hl.eq_of_nhds, hh.eq_of_nhds, sub_self])
  · have hright : c + δ < r := by
      by_contra hn
      exact hnot ⟨le_of_not_gt hleft, le_of_not_gt hn⟩
    have hl := returnOpticalCutoff_eventually_one (x := c - 3 * δ / 4)
      (δ := δ / 4) (r := r) (by linarith) (by linarith)
    have hh := returnOpticalCutoff_eventually_one (x := c + 3 * δ / 4)
      (δ := δ / 4) (r := r) (by linarith) (by linarith)
    exact hr (by simp only [referenceCenteredCutoff, hl.eq_of_nhds, hh.eq_of_nhds, sub_self])

theorem referenceCenteredCutoff_hasCompactSupport (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (referenceCenteredCutoff c δ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (referenceCenteredCutoff_tsupport c hδ)

theorem referenceCenteredCutoff_jet_bound (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ c δ : ℝ, 0 < δ → ∀ r : ℝ,
      |iteratedDeriv n (referenceCenteredCutoff c δ) r| ≤ K * (δ⁻¹) ^ n := by
  obtain ⟨K, hK, hb⟩ := returnOpticalCutoff_iteratedDeriv_bound n
  refine ⟨2 * K * (4 : ℝ) ^ n, by positivity, ?_⟩
  intro c δ hδ r
  have hquarter : 0 < δ / 4 := by positivity
  have he : iteratedDeriv n (referenceCenteredCutoff c δ) r =
      iteratedDeriv n (returnOpticalCutoff (c - 3 * δ / 4) (δ / 4)) r -
        iteratedDeriv n (returnOpticalCutoff (c + 3 * δ / 4) (δ / 4)) r := by
    exact iteratedDeriv_fun_sub
      ((returnOpticalCutoff_contDiff _ _).contDiffAt.of_le (by simp))
      ((returnOpticalCutoff_contDiff _ _).contDiffAt.of_le (by simp))
  rw [he]
  calc
    _ ≤ |iteratedDeriv n (returnOpticalCutoff (c - 3 * δ / 4) (δ / 4)) r| +
        |iteratedDeriv n (returnOpticalCutoff (c + 3 * δ / 4) (δ / 4)) r| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le
          (iteratedDeriv n (returnOpticalCutoff (c - 3 * δ / 4) (δ / 4)) r) (0 : ℝ)
          (iteratedDeriv n (returnOpticalCutoff (c + 3 * δ / 4) (δ / 4)) r)
    _ ≤ K * ((δ / 4)⁻¹) ^ n + K * ((δ / 4)⁻¹) ^ n :=
      add_le_add (hb _ _ hquarter r) (hb _ _ hquarter r)
    _ = (2 * K * (4 : ℝ) ^ n) * (δ⁻¹) ^ n := by
      rw [inv_div, div_eq_mul_inv, mul_pow]
      ring

def referenceMaterialRootCutoff (D : ReferenceData) (c : ℝ) : ℝ → ℝ :=
  referenceCenteredCutoff c (endpointDistance D c / 2)

theorem referenceMaterialRootCutoff_support {D : ReferenceData} {c : ℝ}
    (hc : c ∈ radialCore D) :
    HasCompactSupport (referenceMaterialRootCutoff D c) ∧
      tsupport (referenceMaterialRootCutoff D c) ⊆ radialCore D ∧
      referenceMaterialRootCutoff D c =ᶠ[𝓝 c] fun _ => 1 := by
  have hd : 0 < endpointDistance D c := lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  have hδ : 0 < endpointDistance D c / 2 := by positivity
  refine ⟨referenceCenteredCutoff_hasCompactSupport c hδ, ?_,
    referenceCenteredCutoff_one_germ c hδ⟩
  intro r hr
  have h := referenceCenteredCutoff_tsupport c hδ hr
  have hl : endpointDistance D c ≤ c - D.a := min_le_left _ _
  have hh : endpointDistance D c ≤ D.b - c := min_le_right _ _
  exact ⟨by linarith only [h.1, hl, hd], by linarith only [h.2, hh, hd]⟩

/-- Constants precede the centre. The bound uses its actual physical E0,
not a reindexed sample or an assumption that E0 is at least one. -/
theorem referenceMaterialRootCutoff_material_jet_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K A : ℝ, 0 ≤ K ∧ 0 ≤ A ∧ ∀ c ∈ radialCore D, ∀ r : ℝ,
      |iteratedDeriv n (referenceMaterialRootCutoff D c) r| ≤ K * T.E0 c ^ A := by
  obtain ⟨C, A, hC, hA, hb⟩ := n08_distance_inverse_le_E0 hT
  obtain ⟨K, hK, hjet⟩ := referenceCenteredCutoff_jet_bound n
  refine ⟨K * (2 * C) ^ n, A * (n : ℝ),
    mul_nonneg hK.le (pow_nonneg (by positivity) _),
    mul_nonneg hA (Nat.cast_nonneg _), ?_⟩
  intro c hc r
  have hd : 0 < endpointDistance D c := lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  have hδ : 0 < endpointDistance D c / 2 := by positivity
  have hE : 0 < T.E0 c := (hT.2.1 c hc).2.2.1
  have hinv : (endpointDistance D c / 2)⁻¹ ≤ (2 * C) * T.E0 c ^ A := by
    rw [inv_div, div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (hb c hc) (by norm_num)).trans_eq (by ring)
  calc
    _ ≤ K * ((endpointDistance D c / 2)⁻¹) ^ n := hjet c _ hδ r
    _ ≤ K * ((2 * C) * T.E0 c ^ A) ^ n := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hinv n) hK.le
    _ = (K * (2 * C) ^ n) * T.E0 c ^ (A * (n : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast (T.E0 c ^ A), ← Real.rpow_mul hE.le]
      ring

/-- The same cutoff cost at a true containing cell's original sample.
No component or test support is asserted to lie inside that cell. -/
theorem referenceMaterialRootCutoff_sample_jet_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (n : ℕ) :
    ∃ K A : ℝ, 0 ≤ K ∧ 0 ≤ A ∧ ∀ m c, c ∈ D.cells m → ∀ r : ℝ,
      |iteratedDeriv n (referenceMaterialRootCutoff D c) r| ≤
        K * T.E0 (T.sample m) ^ A := by
  obtain ⟨K, A, hK, hA, hb⟩ := referenceMaterialRootCutoff_material_jet_bound hT n
  obtain ⟨V, P, hV, hP, hv⟩ := materialCell_E0_rpow_same_cell hT hRef hA
  have hs : ∀ m, T.sample m ∈ D.cells m := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  refine ⟨K * V, P, mul_nonneg hK hV.le, hP, ?_⟩
  intro m c hc r
  have hcore : c ∈ radialCore D := hRef.choose_spec.2.1.2.2.2.1 m hc
  exact (hb c hcore r).trans
    ((mul_le_mul_of_nonneg_left (hv m c (T.sample m) hc (hs m)) hK).trans_eq (by ring))

/-- This is a concrete family admitted by the original inverse bound,
with a common constant before every physical root or other core centre. -/
theorem FirstNormalInverseEstimate.materialRootCutoff_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hNormal : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ radialCore D,
      let χ := referenceMaterialRootCutoff D c
      let u := referenceAffineCutoff c χ
      let F : RadialSource := (referenceCompactCosine (referenceAffineCutoffForcing D c χ),
        referenceRow D (referenceCompactCosine u))
      RadialRepresentativeEq D (G F) (referenceCompactCosine u, 0) ∧
      OutputRealization D γ M₁ 0
        (referenceCompactCosine (fun r => χ r + (r - c) * deriv χ r), 0) ∧
      outputNormSquare D γ M₁ 0
        (referenceCompactCosine (fun r => χ r + (r - c) * deriv χ r), 0) ≤
        C ^ 2 * (sourceNormSquare D γ M₀ F +
          sourceNormSquare D γ M₀ (angularPartial F.1, 0)) := by
  obtain ⟨C, hC, hb⟩ := FirstNormalInverseEstimate.compactAffineCutoff_bound
    hD hborder hG hNormal
  refine ⟨C, hC, ?_⟩
  intro c hc
  have hsupport := referenceMaterialRootCutoff_support hc
  exact hb c (referenceMaterialRootCutoff D c)
    (referenceCenteredCutoff_contDiff _ _) hsupport.1 hsupport.2.1

end ContinuousFlexibility.Statements
