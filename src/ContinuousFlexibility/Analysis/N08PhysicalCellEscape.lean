module

public import ContinuousFlexibility.Analysis.MaterialSampleCofinite
public import ContinuousFlexibility.Analysis.MaterialCoordinate
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Escape of the actual physical cells

The positive height tests supply a comparison for a fixed physical-cell
map. Positivity of each individual sample weight and decay at the assigned
labels force that same map to have finite fibres. The actual material
endpoint formula then makes its envelope diverge and its inverse vanish.
No new choice of physical cells or alignment with control labels is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

theorem n08_cofinite_of_positive_weight_tendsto_zero
    {physical : ℕ → ℕ} {w : ℕ → ℝ} (hw : ∀ j, 0 < w j)
    (hlim : Tendsto (fun m => w (physical m)) cofinite (𝓝 0)) :
    Tendsto physical cofinite cofinite := by
  apply Tendsto.cofinite_of_finite_preimage_singleton
  intro j
  have hev : ∀ᶠ m in cofinite, w (physical m) < w j :=
    hlim.eventually_lt_const (hw j)
  have hfinite : {m | ¬ w (physical m) < w j}.Finite := eventually_cofinite.mp hev
  apply hfinite.subset
  intro m hm
  have heq : physical m = j := hm
  change ¬ w (physical m) < w j
  rw [heq]
  exact lt_irrefl _

/-- The model envelope grows along the material endpoint coordinate. -/
theorem n08_tendsto_materialM_atTop : Tendsto materialM atTop atTop := by
  have hp : Tendsto (fun x : ℝ => x ^ ((5 : ℝ) / 2)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hlog : Tendsto (fun x : ℝ => materialLogFactor x ^ (2 : ℕ)) atTop atTop :=
    by simpa only [Function.comp_def] using
      (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp tendsto_materialLogFactor_atTop
  have hprod := hp.atTop_mul_atTop₀ hlog
  have hexponent : Tendsto materialMExponent atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1)) hprod
  unfold materialM
  simpa only [Function.comp_def] using Real.tendsto_exp_atTop.comp hexponent

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology

variable {D : ReferenceData} {T : MaterialData}

theorem n08_materialSample_H_rpow_tendsto_zero
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun m => T.H (T.sample m) ^ γ) cofinite (𝓝 0) := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _⟩ := hdata
  obtain ⟨_, _, _, hleft, hright⟩ := hdecay 0 γ hγ
  apply materialSample_tendsto_zero_of_endpoint_limits hT hD (f := fun r => T.H r ^ γ)
  · simpa only [Real.rpow_zero, mul_one] using hleft
  · simpa only [Real.rpow_zero, mul_one] using hright

/-- Samples may alternate endpoints. Their endpoint distance tends to
zero, and both collars use the same divergent model envelope. -/
theorem n08_materialSample_M_tendsto_atTop
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) :
    Tendsto (fun m => T.M (T.sample m)) cofinite atTop := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    ⟨d0, δ0, hd0, hδ0, _, hleft, hright⟩, _⟩ := hdata
  have hsample := materialSample_mem_radialCore hT hD.choose_spec.2.1
  have hdist := materialSample_endpointDistance_tendsto_zero hT hD
  have hmodel : Tendsto (fun d => Analysis.materialM (Analysis.endpointX d0 d))
      (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [Function.comp_def] using
      Analysis.n08_tendsto_materialM_atTop.comp (Analysis.tendsto_endpointX_atTop hd0)
  apply tendsto_atTop.mpr
  intro B
  have hev : ∀ᶠ d in 𝓝[>] (0 : ℝ), B ≤ Analysis.materialM (Analysis.endpointX d0 d) :=
    hmodel.eventually_ge_atTop B
  obtain ⟨δ, hδ, hδbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  filter_upwards [hdist.eventually_lt_const (lt_min hδ hδ0)] with m hm
  let r := T.sample m
  have hr : r ∈ radialCore D := hsample m
  have hd : 0 < endpointDistance D r :=
    lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hnear : endpointDistance D r < δ := hm.trans_le (min_le_left _ _)
  have hnear0 : endpointDistance D r < δ0 := hm.trans_le (min_le_right _ _)
  have hbound : B ≤ Analysis.materialM (Analysis.endpointX d0 (endpointDistance D r)) :=
    hδbound ⟨hd, hnear⟩
  have hformula : T.M r = Analysis.materialM (Analysis.endpointX d0 (endpointDistance D r)) := by
    by_cases hside : r - D.a ≤ D.b - r
    · have hn : r - D.a < δ0 := by
        simpa only [endpointDistance, min_eq_left hside] using hnear0
      simpa only [endpointDistance, min_eq_left hside] using
        (hleft r ⟨hr.1, by linarith only [hn]⟩).2.2.2
    · have hside' : D.b - r ≤ r - D.a := le_of_not_ge hside
      have hn : D.b - r < δ0 := by
        simpa only [endpointDistance, min_eq_right hside'] using hnear0
      simpa only [endpointDistance, min_eq_right hside'] using
        (hright r ⟨by linarith only [hn], hr.2⟩).2.2.2
  change B ≤ T.M r
  rw [hformula]
  exact hbound

variable {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {base loss : ℕ} {ε : ℝ}

/-- The height comparison from the actual mixed flow tests forces finite
fibres for precisely the supplied physical-cell map. -/
theorem n08_physicalCell_tendsto_cofinite
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε)
    (physical : ℕ → ℕ)
    (hcompare : ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample (physical m)) ^ (33 : ℝ) ≤
        K * T.H (T.sample (C.cell m)) ^ (3 / 8 : ℝ)) :
    Tendsto physical cofinite cofinite := by
  obtain ⟨K, _, hbound⟩ := hcompare
  obtain ⟨_, _, hindex⟩ := hN.2.2.2.2.1
  have hlabel := controlCell_tendsto_cofinite hN.1.1 C.cell hindex
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1
  have hsmall : Tendsto (fun m => T.H (T.sample (physical m)) ^ (33 : ℝ))
      cofinite (𝓝 0) := by
    apply squeeze_zero (fun m => Real.rpow_nonneg (hH (physical m)).le _) hbound
    simpa only [mul_zero, Function.comp_def] using
      ((n08_materialSample_H_rpow_tendsto_zero hT hN.1.1
        (by norm_num : (0 : ℝ) < 3 / 8)).comp hlabel).const_mul K
  exact Analysis.n08_cofinite_of_positive_weight_tendsto_zero
    (physical := physical) (w := fun j => T.H (T.sample j) ^ (33 : ℝ))
    (fun j => Real.rpow_pos_of_pos (hH j) (33 : ℝ)) hsmall

theorem n08_physicalCell_M_tendsto_atTop
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε)
    (physical : ℕ → ℕ)
    (hcompare : ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample (physical m)) ^ (33 : ℝ) ≤
        K * T.H (T.sample (C.cell m)) ^ (3 / 8 : ℝ)) :
    Tendsto (fun m => T.M (T.sample (physical m))) cofinite atTop := by
  simpa only [Function.comp_def] using
    (n08_materialSample_M_tendsto_atTop hT hN.1.1).comp
      (n08_physicalCell_tendsto_cofinite hT hN physical hcompare)

/-- This is the tail factor for the fixed reference-height cutoff term
in the rescaled state's neighborhood estimate. -/
theorem n08_physicalCell_invM_tendsto_zero
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε)
    (physical : ℕ → ℕ)
    (hcompare : ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample (physical m)) ^ (33 : ℝ) ≤
        K * T.H (T.sample (C.cell m)) ^ (3 / 8 : ℝ)) :
    Tendsto (fun m => (T.M (T.sample (physical m)))⁻¹) cofinite (𝓝 0) := by
  simpa only [Function.comp_def] using
    tendsto_inv_atTop_zero.comp (n08_physicalCell_M_tendsto_atTop hT hN physical hcompare)

end ContinuousFlexibility.Statements
