import ContinuousFlexibility.Analysis.N08CircleParameterComparison
import ContinuousFlexibility.Analysis.N08CircleZeroUniform

/-!
# Uniform tail stability from the actual localized height estimates

The fixed reference height is included in the uniform bound. Its localized
norm tends to zero with the physical sample, so both rescaled states remain
in the same N02 domain. The zero-parameter estimate and the fixed-parameter
comparison then control the same diagonal by one quarter.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem n08_decayingHeight_grading_le_state (S : PhysicalSpacesData) (s : ℕ)
    (x : AnnularState S) :
    (S.height (3 / 4 : ℝ)).grading s x.1.1 ≤ stateGrading S s x := by
  change _ ≤ ((S.height (3 / 4 : ℝ)).grading s x.1.1 + ‖x.1.2‖) +
    (‖x.2.1‖ + ((S.circle (3 / 4 : ℝ)).grading s x.2.2.1 +
      (S.circle (3 / 4 : ℝ)).grading s x.2.2.2))
  linarith only [norm_nonneg x.1.2, norm_nonneg x.2.1,
    apply_nonneg ((S.circle (3 / 4 : ℝ)).grading s) x.2.2.1,
    apply_nonneg ((S.circle (3 / 4 : ℝ)).grading s) x.2.2.2]

theorem n08_totalHeight_grading_bound (S : PhysicalSpacesData) (s : ℕ)
    (a x : AnnularState S) :
    (S.height (3 / 4 : ℝ)).grading s x.1.1 ≤ stateGrading S s (x - a) +
      (S.height (3 / 4 : ℝ)).grading s a.1.1 := by
  have h := ((S.height (3 / 4 : ℝ)).grading s).add_le (x.1.1 - a.1.1) a.1.1
  rw [sub_add_cancel] at h
  exact h.trans (add_le_add (n08_decayingHeight_grading_le_state S s (x - a)) le_rfl)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08CircleDiagonal_tail_of_height_localizations
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    (physical : ℕ → ℕ)
    (F : ℕ → (S.height (3 / 4 : ℝ)).Space →L[ℝ] (S.height (3 / 4 : ℝ)).Space)
    (hdecode : ∀ m (u : (S.height (3 / 4 : ℝ)).Space),
      ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
        (S.height (3 / 4 : ℝ)).decode (F m u) =ᶠ[𝓝 (r, θ)]
          (S.height (3 / 4 : ℝ)).decode u)
    (hdecay : ∀ s a : ℕ, ∃ b : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ m (u : (S.height (3 / 4 : ℝ)).Space),
        T.M (T.sample m) ^ a * (S.height (3 / 4 : ℝ)).grading s (F m u) ≤
          K * (T.M (T.sample (physical m)))⁻¹ * (S.height (3 / 4 : ℝ)).grading b u)
    (hescape : Tendsto (fun m => (T.M (T.sample (physical m)))⁻¹) cofinite (𝓝 0)) :
    ∃ b : ℕ, ∃ δ : ℝ, ∃ I : Finset ℕ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C b δ, stateSector S z.1 → ∀ m, m ∉ I →
        |n08CircleDiagonal hS hR z m - 1| ≤ (1 / 4 : ℝ) := by
  classical
  obtain ⟨bp, δp, K, hbp, hδp, hδpε, hK, hparam⟩ :=
    n08CircleDiagonal_parameter_difference_bound hT hS hN hR
  obtain ⟨bz, δz, hbz, hδz, _, hzero⟩ := n08CircleDiagonal_zero_uniform hT hS hN hR
  obtain ⟨bl, A, hA, hF⟩ := hdecay bp bp
  let b := max bp (max bz bl)
  let δ := min δp (min δz 1)
  let H := 1 + (S.height (3 / 4 : ℝ)).grading bl C.referenceState.1.1
  let e (m : ℕ) := A * (T.M (T.sample (physical m)))⁻¹ * H
  have hH : 0 ≤ H := add_nonneg zero_le_one (apply_nonneg _ _)
  have he (m : ℕ) : 0 ≤ e m := mul_nonneg
    (mul_nonneg hA (inv_nonneg.mpr
      (zero_le_one.trans (n08_material_sample_bounds hN.1.1 hT (physical m)).2))) hH
  have ht : Tendsto (fun m => (K + 1) * e m) cofinite (𝓝 0) := by
    simpa only [e, mul_zero, zero_mul] using ((hescape.const_mul A).mul_const H).const_mul (K + 1)
  have htail : ∀ᶠ m in cofinite, (K + 1) * e m < min (δp / 2) (1 / 8 : ℝ) :=
    ht.eventually_lt_const (lt_min (half_pos hδp) (by norm_num))
  have hfinite : {m | ¬ (K + 1) * e m < min (δp / 2) (1 / 8 : ℝ)}.Finite :=
    mem_cofinite.mp htail
  have hδ : 0 < δ := lt_min hδp (lt_min hδz zero_lt_one)
  have hδp' : δ ≤ δp := min_le_left _ _
  have hδz' : δ ≤ δz := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hp : bp ≤ b := le_max_left _ _
  have hz : bz ≤ b := (le_max_left bz bl).trans (le_max_right bp _)
  have hl : bl ≤ b := (le_max_right bz bl).trans (le_max_right bp _)
  refine ⟨b, δ, hfinite.toFinset, hbp.trans hp, hδ, hδp'.trans hδpε, ?_⟩
  intro z hnear hs m hm
  have hsmall : (K + 1) * e m < min (δp / 2) (1 / 8 : ℝ) := by
    by_contra hn
    exact hm (hfinite.mem_toFinset.mpr hn)
  have hraw : (S.height (3 / 4 : ℝ)).grading bl z.1.1.1 ≤ H := by
    have hb := solve_stateGrading_monotone S hl (z.1 - C.referenceState)
    have hstate : stateGrading S bl (z.1 - C.referenceState) ≤ 1 :=
      hb.trans (hnear.1.le.trans hδ1)
    exact (n08_totalHeight_grading_bound S bl C.referenceState z.1).trans
      (by dsimp only [H]; linarith only [hstate])
  have hW : T.M (T.sample m) ^ bp *
      (S.height (3 / 4 : ℝ)).grading bp (F m z.1.1.1) ≤ e m :=
    (hF m z.1.1.1).trans (mul_le_mul_of_nonneg_left hraw
      (mul_nonneg hA (inv_nonneg.mpr
        (zero_le_one.trans (n08_material_sample_bounds hN.1.1 hT (physical m)).2))))
  have heQ : e m ≤ (K + 1) * e m := by nlinarith only [hK, he m]
  have hcut : (S.height (3 / 4 : ℝ)).grading bp (F m z.1.1.1) ≤ δp / 2 := by
    have hfirst : (S.height (3 / 4 : ℝ)).grading bp (F m z.1.1.1) ≤
        T.M (T.sample m) ^ bp * (S.height (3 / 4 : ℝ)).grading bp (F m z.1.1.1) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (n08_material_sample_bounds hN.1.1 hT m).2)
        (apply_nonneg ((S.height (3 / 4 : ℝ)).grading bp) (F m z.1.1.1))
    exact (hfirst.trans (hW.trans heQ)).trans (hsmall.le.trans (min_le_left _ _))
  obtain ⟨c, hc⟩ := n08_chiLeft_constant_germ_on_component hS hN m
  have hdiff := hparam z.1 z.2 (n08_stateNeighborhood_mono hp hδp' hnear) hs m
    (F m z.1.1.1) hcut (hdecode m z.1.1.1) (fun r hr => ⟨c, hc r hr⟩)
  have hdiffsmall : |n08CircleDiagonal hS hR z m - n08CircleDiagonal hS hR (z.1, 0) m| ≤
      (1 / 8 : ℝ) := by
    have hmul : K * T.M (T.sample m) ^ bp *
        (S.height (3 / 4 : ℝ)).grading bp (F m z.1.1.1) ≤ K * e m := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hW hK
    have hQ : K * e m ≤ (K + 1) * e m := by nlinarith only [he m]
    exact (hdiff.trans (hmul.trans hQ)).trans (hsmall.le.trans (min_le_right _ _))
  have hzeroNear : (z.1, 0) ∈ stateNeighborhood S C bz δz :=
    ⟨(solve_stateGrading_monotone S hz _).trans_lt (hnear.1.trans_le hδz'),
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hδz⟩
  calc
    _ = |(n08CircleDiagonal hS hR z m - n08CircleDiagonal hS hR (z.1, 0) m) +
        (n08CircleDiagonal hS hR (z.1, 0) m - 1)| := by congr 1; ring
    _ ≤ _ + _ := abs_add_le _ _
    _ ≤ (1 / 8 : ℝ) + 1 / 8 := add_le_add hdiffsmall (hzero z.1 hzeroNear hs m)
    _ = _ := by norm_num

end ContinuousFlexibility.Statements
