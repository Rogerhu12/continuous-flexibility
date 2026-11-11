import ContinuousFlexibility.Analysis.ControlCellEndpointBounds
import ContinuousFlexibility.Analysis.MaterialSampleCofinite

/-!
# The actual material samples in the discrete endpoint coordinate

Outside a finite set of samples the material weights are exactly the
prescribed endpoint functions.  Their endpoint coordinate differs from
the actual reference-cell index by one fixed constant.  A separate
finite-exception lemma turns subsequent eventual estimates into uniform
estimates with a positive constant.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

theorem exists_pos_mul_bound_of_cofinite
    {f g : ℕ → ℝ} (hg : ∀ m, 0 < g m) {K : ℝ}
    (hbound : ∀ᶠ m in cofinite, f m ≤ K * g m) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, f m ≤ C * g m := by
  classical
  have hfinite : {m : ℕ | ¬ f m ≤ K * g m}.Finite := eventually_cofinite.mp hbound
  let bad := hfinite.toFinset
  let S := ∑ m ∈ bad, |f m / g m|
  let C := max K (1 + S)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hC : 0 < C := (by linarith only [hS] : 0 < 1 + S).trans_le (le_max_right _ _)
  refine ⟨C, hC, fun m => ?_⟩
  by_cases hm : f m ≤ K * g m
  · exact hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hg m).le)
  · have hmb : m ∈ bad := hfinite.mem_toFinset.mpr hm
    have hterm : |f m / g m| ≤ S :=
      Finset.single_le_sum (fun _ _ => abs_nonneg _) hmb
    have hratio : f m / g m ≤ C :=
      (le_abs_self _).trans (hterm.trans ((by linarith : S ≤ 1 + S).trans (le_max_right _ _)))
    exact (div_le_iff₀ (hg m)).mp hratio

theorem cellIndex_eventually_ge_real
    {D : ReferenceData} (hRef : IsAccumulatingProfile D) (R : ℝ) :
    ∀ᶠ m in cofinite, R ≤ (D.cellIndex m : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨_, hbounds⟩ := hRef
  have hfinite : {m : ℕ | D.cellIndex m ≤ N}.Finite := hbounds.2.2.2.2.1 N
  filter_upwards [hfinite.eventually_cofinite_notMem] with m hm
  have hn : N < D.cellIndex m := lt_of_not_ge hm
  have hcast : (N : ℝ) ≤ D.cellIndex m := by exact_mod_cast hn.le
  exact hN.trans hcast

/-- The same endpoint scale and the same coordinate error work for H,
E0 and M at every sufficiently late actual sample. -/
theorem materialSample_eventually_endpoint_models
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ d0 L : ℝ, 0 < d0 ∧ 0 ≤ L ∧ ∀ᶠ m in cofinite,
      let x := endpointX d0 (endpointDistance D (T.sample m))
      T.H (T.sample m) = materialH x ∧
        T.E0 (T.sample m) = materialE0 x ∧
        T.M (T.sample m) = materialM x ∧
        |x - (D.cellIndex m : ℝ)| ≤ L := by
  have hdata := hT
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, hend, _, _, _, _, hsamp, _, hcomp⟩
  obtain ⟨d0, δ, hd0, hδ, hδbound, hleft, hright⟩ := hend
  obtain ⟨C, A, hC, _, hcmp⟩ := hcomp
  obtain ⟨_, hbounds⟩ := hRef
  let L := C + Real.sqrt |Real.log d0|
  have hL : 0 ≤ L := add_nonneg hC.le (Real.sqrt_nonneg _)
  refine ⟨d0, L, hd0, hL, ?_⟩
  have hnear : ∀ᶠ m in cofinite, endpointDistance D (T.sample m) < min δ 1 :=
    (materialSample_endpointDistance_tendsto_zero hT hRef).eventually_lt_const
      (lt_min hδ zero_lt_one)
  filter_upwards [hnear] with m hm
  dsimp only
  have hcore : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hbounds.2.1 m
  have hd : 0 < endpointDistance D (T.sample m) :=
    lt_min (sub_pos.mpr hcore.1) (sub_pos.mpr hcore.2)
  have hdδ : endpointDistance D (T.sample m) < δ := hm.trans_le (min_le_left _ _)
  have hdd0 : endpointDistance D (T.sample m) < d0 :=
    hdδ.trans (hδbound.trans_le (min_le_left _ _))
  have hd1 : endpointDistance D (T.sample m) < 1 := hm.trans_le (min_le_right _ _)
  have hscale := abs_endpointX_scale_sub_le hd0 hd hdd0 hd1
  have hindex := (hcmp m (T.sample m) (hsamp m)).1
  have hclose :
      |endpointX d0 (endpointDistance D (T.sample m)) - (D.cellIndex m : ℝ)| ≤ L := by
    calc
      _ ≤ |endpointX d0 (endpointDistance D (T.sample m)) -
          endpointX 1 (endpointDistance D (T.sample m))| +
          |endpointX 1 (endpointDistance D (T.sample m)) - (D.cellIndex m : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ Real.sqrt |Real.log d0| + C := add_le_add hscale hindex
      _ = L := by dsimp only [L]; ring
  have hmodels :
      T.H (T.sample m) = materialH (endpointX d0 (endpointDistance D (T.sample m))) ∧
        T.E0 (T.sample m) = materialE0 (endpointX d0 (endpointDistance D (T.sample m))) ∧
        T.M (T.sample m) = materialM (endpointX d0 (endpointDistance D (T.sample m))) := by
    by_cases hside : T.sample m - D.a ≤ D.b - T.sample m
    · have hnearLeft : T.sample m - D.a < δ := by
        simpa only [endpointDistance, min_eq_left hside] using hdδ
      have h := hleft (T.sample m) ⟨hcore.1, by linarith only [hnearLeft]⟩
      simpa only [endpointDistance, min_eq_left hside] using
        And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2)
    · have hside' : D.b - T.sample m ≤ T.sample m - D.a := le_of_not_ge hside
      have hnearRight : D.b - T.sample m < δ := by
        simpa only [endpointDistance, min_eq_right hside'] using hdδ
      have h := hright (T.sample m) ⟨by linarith only [hnearRight], hcore.2⟩
      simpa only [endpointDistance, min_eq_right hside'] using
        And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2)
  exact ⟨hmodels.1, hmodels.2.1, hmodels.2.2, hclose⟩

end ContinuousFlexibility.Statements
