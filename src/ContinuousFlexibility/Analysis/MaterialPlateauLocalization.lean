import ContinuousFlexibility.Analysis.MaterialPlateauRadialLoss
import ContinuousFlexibility.Analysis.MaterialPlateauSize
import ContinuousFlexibility.Analysis.MaterialPlateauJets
import ContinuousFlexibility.Analysis.MaterialHeightCutoff

/-!
# Actual plateau localization of an arbitrary physical height

The radial cutoff is transported through the supplied material radius.
Every fixed derivative of this multiplier is bounded by one material
weight, uniformly over actual containing cells. Multiplication preserves
the physical height model and the full open component germ.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def materialPlateauCutoff (T : MaterialData) (l r δ : ℝ) : ℝ → ℝ :=
  fun x => radialPlateauCutoff l r δ (T.radius x)

theorem materialPlateauCutoff_contDiff {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (l r δ : ℝ) :
    ContDiff ℝ ∞ (materialPlateauCutoff T l r δ) := by
  have heq : materialPlateauCutoff T l r δ = radialPlateauCutoff l r δ ∘ T.radius := rfl
  rw [heq]
  exact (radialPlateauCutoff_contDiff l r δ).comp hT.2.2.2.2.2.2.1

theorem materialPlateauCutoff_iteratedDeriv_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : ℝ,
      |iteratedDeriv n (materialPlateauCutoff T l r δ) x| ≤ K * δ⁻¹ ^ n := by
  have hc : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have hb : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : ℝ, |iteratedDeriv i (fun _ : ℝ => (1 : ℝ)) x| ≤ K := by
    intro i
    refine ⟨1, zero_le_one, fun x => ?_⟩
    simp only [iteratedDeriv_const]
    split_ifs <;> norm_num
  obtain ⟨K, hK, hbound⟩ := radialPlateauProduct_materialJet_bound hT hc hb n
  refine ⟨K, hK, fun l r δ hδ hδ1 x => ?_⟩
  have heq : (fun y : ℝ =>
      radialPlateauProduct (fun _ : ℝ => (1 : ℝ)) l r δ (T.radius y)) =
      materialPlateauCutoff T l r δ := by
    funext y
    simp only [radialPlateauProduct, materialPlateauCutoff, mul_one]
  simpa only [heq] using hbound l r δ hδ hδ1 x

theorem materialPlateauCutoff_iteratedDeriv_zero_off_support
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {l r δ x : ℝ} (hδ : 0 < δ)
    (hx : T.radius x ∉ Icc (l - δ) (r + δ)) (n : ℕ) :
    iteratedDeriv n (materialPlateauCutoff T l r δ) x = 0 := by
  have hn : ∀ᶠ y : ℝ in 𝓝 x, T.radius y ∉ Icc (l - δ) (r + δ) :=
    hT.2.2.2.2.2.2.1.continuous.continuousAt.eventually
      (isClosed_Icc.isOpen_compl.mem_nhds hx)
  have heq : materialPlateauCutoff T l r δ =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
    filter_upwards [hn] with y hy
    exact radialPlateauCutoff_zero hδ (fun h => hy ⟨h.1.le, h.2.le⟩)
  simpa only [iteratedDeriv_const_zero, Pi.zero_apply] using heq.iteratedDeriv_eq n

/-- The fixed derivative order affects the constant, while the material
power is exactly one for every order. -/
theorem materialPlateauCutoff_iteratedDeriv_bound_by_M
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j → ∀ x : ℝ,
      |iteratedDeriv n (materialPlateauCutoff T l r (endpointPlateauWidth D l r)) x| ≤
        K * T.M (T.radius x) := by
  obtain ⟨K₀, hK₀, hjet⟩ := materialPlateauCutoff_iteratedDeriv_bound hT n
  obtain ⟨Kd, hKd, hwidth⟩ := materialCell_plateau_inverse_width_bound hD
  obtain ⟨Kr, A, hKr, hA, hradial⟩ := materialCell_plateau_radial_weight_bound hD hT
    (Nat.cast_nonneg (α := ℝ) (2 * n))
  have hmaterial := hT
  obtain ⟨_, _, _, _, _, _, _, hinside, _, _, _, henvelope, _⟩ := hmaterial
  obtain ⟨Ke, hKe, hE⟩ := henvelope A
  let K : ℝ := K₀ * Kd ^ n * Kr * Ke + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro j l r hl hlr hr hcell x
  have hδ := endpointPlateauWidth_pos hl hr
  have hδ1 := endpointPlateauWidth_le_one D l r
  have hM : 0 ≤ T.M (T.radius x) :=
    zero_le_one.trans (hT.2.1 _ (hinside x).1).2.2.2
  by_cases hx : T.radius x ∈
      Icc (l - endpointPlateauWidth D l r) (r + endpointPlateauWidth D l r)
  · have hpow : (endpointPlateauWidth D l r)⁻¹ ^ n ≤
        Kd ^ n * radialE (D.cellIndex j) ^ (2 * n) := by
      calc
        _ ≤ (Kd * radialE (D.cellIndex j) ^ 2) ^ n :=
          pow_le_pow_left₀ (inv_pos.mpr hδ).le (hwidth j l r hl hlr hr hcell) n
        _ = _ := by rw [mul_pow, ← pow_mul]
    have hR : radialE (D.cellIndex j) ^ (2 * n) ≤ Kr * T.E0 (T.radius x) ^ A := by
      simpa only [Real.rpow_natCast] using hradial j l r hl hlr hr hcell (T.radius x) hx
    have hR' : radialE (D.cellIndex j) ^ (2 * n) ≤ Kr * (Ke * T.M (T.radius x)) :=
      hR.trans (mul_le_mul_of_nonneg_left (hE _ (hinside x).1) hKr.le)
    calc
      _ ≤ K₀ * (endpointPlateauWidth D l r)⁻¹ ^ n := hjet l r _ hδ hδ1 x
      _ ≤ K₀ * (Kd ^ n * radialE (D.cellIndex j) ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left hpow hK₀
      _ ≤ K₀ * (Kd ^ n * (Kr * (Ke * T.M (T.radius x)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hR' (pow_nonneg hKd.le n)) hK₀
      _ ≤ K * T.M (T.radius x) := by dsimp only [K]; nlinarith only [hM]
  · rw [materialPlateauCutoff_iteratedDeriv_zero_off_support hT hδ hx n, abs_zero]
    exact mul_nonneg hK.le hM

def radialPlateauLocalization (D : ReferenceData) (T : MaterialData)
    (l r : ℝ) (f : PolarPoint → ℝ) : PolarPoint → ℝ :=
  materialCutoffHeight T (materialPlateauCutoff T l r (endpointPlateauWidth D l r)) f

theorem radialPlateauLocalization_member {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : HeightMember D T γ f) {l r : ℝ} (hl : D.a < l) (hr : r < D.b) :
    HeightMember D T γ (radialPlateauLocalization D T l r f) := by
  apply materialCutoffHeight_member_of_bounded_jets hT hf (materialPlateauCutoff_contDiff hT _ _ _)
  intro n
  obtain ⟨K, hK, hb⟩ := materialPlateauCutoff_iteratedDeriv_bound hT n
  have hδ := endpointPlateauWidth_pos hl hr
  refine ⟨K * (endpointPlateauWidth D l r)⁻¹ ^ n, by positivity, ?_⟩
  exact hb l r _ hδ (endpointPlateauWidth_le_one D l r)

theorem radialPlateauLocalization_eq_germ {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (f : PolarPoint → ℝ)
    {l r t : ℝ} (hl : D.a < l) (hr : r < D.b) (ht : t ∈ Ioo l r) (θ : ℝ) :
    radialPlateauLocalization D T l r f =ᶠ[𝓝 (t, θ)] f := by
  have hn : ∀ᶠ p : PolarPoint in 𝓝 (t, θ), p.1 ∈ Ioo l r :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds ht)
  filter_upwards [hn] with p hp
  have hcore : p.1 ∈ Ioo D.a D.b := ⟨hl.trans hp.1, hp.2.trans hr⟩
  have hback := hT.2.2.2.2.2.2.2.2.1 p.1 hcore
  simp only [radialPlateauLocalization, materialCutoffHeight, materialPlateauCutoff,
    hback, radialPlateauCutoff_one (endpointPlateauWidth_pos hl hr) ⟨hp.1.le, hp.2.le⟩,
    one_mul]

end ContinuousFlexibility.Statements
