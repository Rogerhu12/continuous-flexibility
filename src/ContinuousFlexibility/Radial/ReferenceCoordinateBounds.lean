import ContinuousFlexibility.Radial.ReferenceCoordinateScaffold

/-!
# Accumulating bounds after coordinate and height surgery

Outside a compact subset of the new open annulus, the new profile is
locally an exact radius and height rescaling of the original profile.
The two height factors and two slopes can be chosen independently; only
one common finite bound is used.  In the compact middle, smoothness and
positivity give bounds for all jets, and local finiteness bounds the
labels of the cells meeting that middle.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem coordinateJet_eq_iteratedDeriv (s : ℕ) (f : ℝ → ℝ) :
    radialJet s f = iteratedDeriv s f := by
  induction s with
  | zero => exact iteratedDeriv_zero.symm
  | succ s ih => rw [radialJet, ih, iteratedDeriv_succ]

private theorem coordinateJet_germ {f g : ℝ → ℝ} {r : ℝ}
    (h : f =ᶠ[𝓝 r] g) (s : ℕ) : radialJet s f r = radialJet s g r := by
  simpa only [coordinateJet_eq_iteratedDeriv] using h.iteratedDeriv_eq s

private theorem coordinate_inverse_jets_continuousOn
    {w : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ x ∈ U, 0 < w x) (s : ℕ) :
    ContinuousOn (radialJet s (fun x => (w x)⁻¹)) U := by
  rw [coordinateJet_eq_iteratedDeriv]
  have hi : ContDiffOn ℝ ∞ (fun x => (w x)⁻¹) U :=
    hw.contDiffOn.inv (fun x hx => (hpos x hx).ne')
  have hc := hi.continuousOn_iteratedDerivWithin (m := s) (by simp) hU.uniqueDiffOn
  exact hc.congr (iteratedDerivWithin_of_isOpen hU).symm

private theorem coordinate_scalar_factor {A c M : ℝ}
    (hM : 0 ≤ M) (hA : |A| ≤ M) (hc : |c| ≤ M) (s : ℕ) :
    |A * c ^ s| ≤ M ^ (s + 1) := by
  rw [abs_mul, abs_pow]
  calc
    _ ≤ M * M ^ s :=
      mul_le_mul hA (pow_le_pow_left₀ (abs_nonneg c) hc s)
        (pow_nonneg (abs_nonneg c) s) hM
    _ = M ^ (s + 1) := by rw [pow_succ]; ring

/-- Independent affine tail rescalings and arbitrary smooth positive
interior surgery preserve every accumulating-profile estimate.  The
geometric hypothesis is only the ordinary profile geometry supplied by
the gluing; all partition, trace and quantitative bounds are proved here. -/
theorem isAccumulatingProfile_coordinateSurgery
    {D : ReferenceData} (e : ℝ ≃o ℝ) {w phi : ℝ → ℝ} {K : Set ℝ} {L M : ℝ}
    (hD : IsAccumulatingProfile D) (hIndex : ∀ m, 1 ≤ D.cellIndex m)
    (he : ContDiff ℝ ∞ (fun r => e r)) (hL : 1 ≤ L)
    (hforward : ∀ x y : ℝ, |e x - e y| ≤ L * |x - y|)
    (hbackward : ∀ x y : ℝ, |x - y| ≤ L * |e x - e y|)
    (hNew : RadialProfileGeometry (replaceReferenceProfile (coordinateReference D e) w phi))
    (hK : IsCompact K) (hKcore : K ⊆ radialCore (coordinateReference D e))
    (hM : 1 ≤ M)
    (hTail : ∀ r ∈ radialCore (coordinateReference D e), r ∉ K → ∃ A c : ℝ, 0 < A ∧ |A| ≤ M ∧ A⁻¹ ≤ M ∧ |c| ≤ M ∧
      e r = c * r ∧ w =ᶠ[𝓝 r] fun x => A * D.w (c * x)) :
    IsAccumulatingProfile (replaceReferenceProfile (coordinateReference D e) w phi) := by
  classical
  rcases hD with ⟨C, hGeo, hPart, hC, hNE, hFin, hLoc, hDist,
    hLower, hJet, hInvJet, hWidth, hAbsorb, hTrace⟩
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hPart' := radialPartition_coordinateReference e he hPart
  have hLoc' := coordinateReference_cells_locallyFinite e hLoc
  have hNE' (m : ℕ) : ((coordinateReference D e).cells m).Nonempty := by
    obtain ⟨r, hr⟩ := hNE m
    refine ⟨e.symm r, ?_⟩
    change e (e.symm r) ∈ D.cells m
    simpa only [e.apply_symm_apply] using hr
  have hw : ContDiff ℝ ∞ w := hNew.2.2.1.1
  have hpos : ∀ r ∈ radialCore (coordinateReference D e), 0 < w r :=
    hNew.2.2.2.2.1
  have hBounds : ∀ s : ℕ, ∃ J : ℝ, 1 ≤ J ∧ ∀ r ∈ K,
      |radialJet s w r| ≤ J ∧ |radialJet s (fun x => (w x)⁻¹) r| ≤ J := by
    intro s
    have hc : ContinuousOn (radialJet s w) K := by
      rw [coordinateJet_eq_iteratedDeriv]
      exact (hw.continuous_iteratedDeriv s (by simp)).continuousOn
    obtain ⟨Jw, hJw⟩ := hK.exists_bound_of_continuousOn hc
    obtain ⟨Ji, hJi⟩ := hK.exists_bound_of_continuousOn
      ((coordinate_inverse_jets_continuousOn isOpen_Ioo hw hpos s).mono hKcore)
    refine ⟨max 1 (max Jw Ji), le_max_left _ _, ?_⟩
    intro r hr
    constructor
    · have hh : |radialJet s w r| ≤ Jw := by
        simpa only [Real.norm_eq_abs] using hJw r hr
      exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))
    · have hh : |radialJet s (fun x => (w x)⁻¹) r| ≤ Ji := by
        simpa only [Real.norm_eq_abs] using hJi r hr
      exact hh.trans ((le_max_right _ _).trans (le_max_right _ _))
  choose J hJ hJBounds using hBounds
  let F : Finset ℕ := (hLoc' K hK hKcore).toFinset
  let N : ℕ := F.sup D.cellIndex
  let P : ℝ := (N : ℝ) ^ (5 / 2 : ℝ)
  have hAffected (m : ℕ) (r : ℝ) (hr : r ∈ (coordinateReference D e).cells m)
      (hKr : r ∈ K) : D.cellIndex m ≤ N := by
    have hm : m ∈ F := by
      simp only [F, Set.Finite.mem_toFinset]
      exact ⟨r, hr, hKr⟩
    exact Finset.le_sup hm
  let C' : ℕ → ℝ := fun s =>
    1 + L * C 0 + C s + M + J s * exp P + J s + J 0 + M ^ (s + 1) * C s
  have hJpos (s : ℕ) : 0 < J s := zero_lt_one.trans_le (hJ s)
  have hTerms (s : ℕ) :
      0 ≤ L * C 0 ∧ 0 ≤ J s * exp P ∧ 0 ≤ M ^ (s + 1) * C s :=
    ⟨mul_nonneg hLpos.le (hC 0).le, mul_nonneg (hJpos s).le (exp_pos P).le,
      mul_nonneg (pow_nonneg hMpos.le _) (hC s).le⟩
  have hC' (s : ℕ) : 0 < C' s := by
    dsimp only [C']
    linarith [((hTerms s).1), ((hTerms s).2.1), ((hTerms s).2.2), hC s, hMpos, hJpos s, hJpos 0]
  have hCC' (s : ℕ) : C s ≤ C' s := by
    dsimp only [C']
    linarith [((hTerms s).1), ((hTerms s).2.1), ((hTerms s).2.2), hMpos, hJpos s, hJpos 0]
  have hCM (s : ℕ) : C s + M ≤ C' s := by
    dsimp only [C']
    linarith [((hTerms s).1), ((hTerms s).2.1), ((hTerms s).2.2), hJpos s, hJpos 0]
  have hLC' (s : ℕ) : L * C 0 ≤ C' s := by
    dsimp only [C']
    linarith [((hTerms s).1), ((hTerms s).2.1), ((hTerms s).2.2), hC s, hMpos, hJpos s, hJpos 0]
  have hJC' (s : ℕ) : J s ≤ C' s := by
    dsimp only [C']
    linarith [((hTerms s).1), ((hTerms s).2.1), ((hTerms s).2.2), hC s, hMpos, hJpos 0]
  have hJ0C' (s : ℕ) : J 0 ≤ C' s := by
    dsimp only [C']
    linarith [((hTerms s).1), ((hTerms s).2.1), ((hTerms s).2.2), hC s, hMpos, hJpos s]
  have hJE (s : ℕ) : J s * exp P ≤ C' s := by
    dsimp only [C']
    linarith [((hTerms s).1), ((hTerms s).2.1), ((hTerms s).2.2), hC s, hMpos, hJpos s, hJpos 0]
  have hBC' (s : ℕ) : M ^ (s + 1) * C s ≤ C' s := by
    dsimp only [C']
    linarith [((hTerms s).1), ((hTerms s).2.1), ((hTerms s).2.2), hC s, hMpos, hJpos s, hJpos 0]
  have hE (n : ℕ) : 1 ≤ radialE n :=
    one_le_exp_iff.mpr (radialQ_nonneg n)
  have hnSq (m : ℕ) : 1 ≤ (D.cellIndex m : ℝ) ^ 2 := by
    have hn : (1 : ℝ) ≤ D.cellIndex m := by exact_mod_cast hIndex m
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn 2
  refine ⟨C', hNew, hPart', hC', hNE', hFin, hLoc', ?_, ?_, ?_, ?_, ?_,
    hAbsorb, radialTraceScaffold_coordinateReference e hLpos hforward hTrace⟩
  · intro m r hr
    obtain ⟨hl, hu⟩ :=
      coordinateReference_gaussian_distance D e hLpos hforward hbackward
        hPart.2.2.2.1 hDist m r hr
    exact ⟨(mul_le_mul_of_nonneg_right
      (inv_anti₀ (mul_pos hLpos (hC 0)) (hLC' 0)) (exp_pos _).le).trans hl,
      hu.trans (mul_le_mul_of_nonneg_right (hLC' 0) (exp_pos _).le)⟩
  · intro m r hr
    change exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) -
      C' 0 * (D.cellIndex m : ℝ) ^ 2) ≤ w r
    have hrOld : e r ∈ D.cells m := hr
    by_cases hKr : r ∈ K
    · have hwr : 0 < w r := hpos r (hKcore hKr)
      have hInv : (w r)⁻¹ ≤ J 0 := by
        simpa only [radialJet, abs_of_pos (inv_pos.mpr hwr)] using (hJBounds 0 r hKr).2
      have hp : 0 ≤ (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hCt : C' 0 ≤ C' 0 * (D.cellIndex m : ℝ) ^ 2 :=
        le_mul_of_one_le_right (hC' 0).le (hnSq m)
      have hCe : C' 0 ≤ exp (C' 0 * (D.cellIndex m : ℝ) ^ 2) :=
        hCt.trans ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _))
      apply (inv_le_inv₀ hwr (exp_pos _)).mp
      rw [← exp_neg]
      change (w r)⁻¹ ≤ exp (-(-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) -
        C' 0 * (D.cellIndex m : ℝ) ^ 2))
      have hexp : C' 0 * (D.cellIndex m : ℝ) ^ 2 ≤
          -(-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) -
            C' 0 * (D.cellIndex m : ℝ) ^ 2) := by linarith
      exact hInv.trans ((hJ0C' 0).trans (hCe.trans (exp_le_exp.mpr hexp)))
    · obtain ⟨A, c, hA, hAM, hAI, hc, her, hg⟩ := hTail r (hPart'.2.2.2.1 m hr) hKr
      let T : ℝ := (C' 0 - C 0) * (D.cellIndex m : ℝ) ^ 2
      have hT : M ≤ T := by
        have hbase : M ≤ C' 0 - C 0 := by linarith [hCM 0]
        have hterm := mul_le_mul_of_nonneg_left (hnSq m)
          (hMpos.le.trans hbase)
        dsimp only [T]
        nlinarith
      have hAi : A⁻¹ ≤ exp T :=
        hAI.trans (hT.trans ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp T)))
      have hAe : exp (-T) ≤ A := by
        apply (inv_le_inv₀ hA (exp_pos (-T))).mp
        simpa only [← exp_neg, neg_neg] using hAi
      calc
        exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) -
            C' 0 * (D.cellIndex m : ℝ) ^ 2) =
            exp (-T) * exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) -
              C 0 * (D.cellIndex m : ℝ) ^ 2) := by
          rw [← exp_add]
          congr 1
          dsimp only [T]
          ring
        _ ≤ A * exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) -
            C 0 * (D.cellIndex m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hAe (exp_pos _).le
        _ ≤ A * D.w (e r) :=
          mul_le_mul_of_nonneg_left (hLower m (e r) hrOld) hA.le
        _ = w r := by rw [her]; exact hg.eq_of_nhds.symm
  · intro m r hr s
    change |radialJet s w r| ≤ C' s *
      exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) + C' s * (D.cellIndex m : ℝ) ^ 2)
    have hrOld : e r ∈ D.cells m := hr
    by_cases hKr : r ∈ K
    · have hLabel : (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) ≤ P :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hAffected m r hr hKr)
          (by norm_num)
      have hJe : J s ≤ C' s * exp (-P) := by
        have h := (le_div_iff₀ (exp_pos P)).mpr (hJE s)
        simpa only [div_eq_mul_inv, exp_neg] using h
      apply (hJBounds s r hKr).1.trans
      apply hJe.trans
      apply mul_le_mul_of_nonneg_left _ (hC' s).le
      apply exp_le_exp.mpr
      have hTerm := mul_nonneg (hC' s).le (sq_nonneg (D.cellIndex m : ℝ))
      linarith
    · obtain ⟨A, c, hA, hAM, hAI, hc, her, hg⟩ := hTail r (hPart'.2.2.2.1 m hr) hKr
      have hj : radialJet s w r =
          A * c ^ s * radialJet s D.w (e r) := by
        rw [coordinateJet_germ hg s]
        simpa only [← her] using congrFun (radialJet_scalar_coordinate s D.w A c) r
      rw [hj, abs_mul]
      have hf := coordinate_scalar_factor hMpos.le hAM hc s
      have hexp : exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) +
            C s * (D.cellIndex m : ℝ) ^ 2) ≤
          exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) +
            C' s * (D.cellIndex m : ℝ) ^ 2) := by
        apply exp_le_exp.mpr
        have ht := mul_le_mul_of_nonneg_right (hCC' s) (sq_nonneg (D.cellIndex m : ℝ))
        linarith
      calc
        _ ≤ M ^ (s + 1) * (C s *
            exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) +
              C s * (D.cellIndex m : ℝ) ^ 2)) :=
          mul_le_mul hf (hJet m (e r) hrOld s)
            (abs_nonneg _) (pow_nonneg hMpos.le _)
        _ = (M ^ (s + 1) * C s) *
            exp (-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) +
              C s * (D.cellIndex m : ℝ) ^ 2) := by ring
        _ ≤ _ := mul_le_mul (hBC' s) hexp (exp_pos _).le (hC' s).le
  · intro m r hr s
    change |radialJet s (fun x => (w x)⁻¹) r| ≤
      C' s * radialE (D.cellIndex m) ^ C' s
    have hrOld : e r ∈ D.cells m := hr
    by_cases hKr : r ∈ K
    · exact (hJBounds s r hKr).2.trans ((hJC' s).trans
        (le_mul_of_one_le_right (hC' s).le
          (Real.one_le_rpow (hE _) (hC' s).le)))
    · obtain ⟨A, c, hA, hAM, hAI, hc, her, hg⟩ := hTail r (hPart'.2.2.2.1 m hr) hKr
      have hgi : (fun x => (w x)⁻¹) =ᶠ[𝓝 r]
          fun x => A⁻¹ * (D.w (c * x))⁻¹ := by
        filter_upwards [hg] with x hx
        rw [hx, mul_inv_rev]
        ring
      have hj : radialJet s (fun x => (w x)⁻¹) r =
          A⁻¹ * c ^ s * radialJet s (fun x => (D.w x)⁻¹) (e r) := by
        rw [coordinateJet_germ hgi s]
        simpa only [← her] using congrFun
          (radialJet_scalar_coordinate s (fun x => (D.w x)⁻¹) A⁻¹ c) r
      rw [hj, abs_mul]
      have hAIM : |A⁻¹| ≤ M := by
        simpa only [abs_of_pos (inv_pos.mpr hA)] using hAI
      have hf := coordinate_scalar_factor hMpos.le hAIM hc s
      calc
        _ ≤ M ^ (s + 1) * (C s * radialE (D.cellIndex m) ^ C s) :=
          mul_le_mul hf (hInvJet m (e r) hrOld s)
            (abs_nonneg _) (pow_nonneg hMpos.le _)
        _ = (M ^ (s + 1) * C s) * radialE (D.cellIndex m) ^ C s := by ring
        _ ≤ _ := mul_le_mul (hBC' s)
          (Real.rpow_le_rpow_of_exponent_le (hE _) (hCC' s))
          (Real.rpow_nonneg (zero_le_one.trans (hE _)) _) (hC' s).le
  · intro m
    obtain ⟨l, h, hsub, hlen⟩ :=
      coordinateReference_cell_widths D e hLpos.le hbackward hNE hWidth m
    exact ⟨l, h, hsub, hlen.trans
      (mul_le_mul_of_nonneg_right (hLC' 0) (exp_pos _).le)⟩

end ContinuousFlexibility.Radial
