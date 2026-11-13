import ContinuousFlexibility.Analysis.N04NegativeChartStateOpticalFactor
import ContinuousFlexibility.Analysis.N01cOpticalMaterialBounds

/-!
# Material bounds for the genuine divided optical square

The actual state direction retains its single height weight through
both sample changes: from the decoded control sample to its component
host, and then to the sample of the selected atlas half. The absolute
state-square bound is used only for unmarked factors; the separate
direction bound keeps the full height gain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

/-- All ordinary jets of the actual affine direction have one unchanged
height factor and require only the level-zero state seminorm. -/
theorem control_direction_material_jets (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m side t,
      t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) → ∀ v : AnnularState W.S,
        |stateKappa W.S v m * iteratedDeriv n (F.control m side) t| ≤
          B * W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
            W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ A *
              stateGrading W.S 0 v := by
  obtain ⟨Bc, Ac, hBc, hAc, hcontrol⟩ := F.control_jets n
  obtain ⟨J, hJ, hindex⟩ := W.through03.1.1.2.2.2.2.1
  obtain ⟨Cs, Ps, hCs, hPs, hshift⟩ :=
    materialSample_weight_bound_sameExponent W.hT W.radial.1 (3 / 4 : ℝ) Ac hJ.le
  obtain ⟨Ct, Pt, hCt, hPt, hhost⟩ :=
    n04bActualTypedAtlas_negative_host_sample_weights
      W.hT W.hS W.through03 W.field e (3 / 4 : ℝ) 0 Ps hPs.le
  have hs : ∀ j, W.T.sample j ∈ W.D.cells j := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := W.hT
    exact hs
  let c : ℝ := (1 / Real.pi) * Real.sqrt Real.pi
  have hc : 0 < c := mul_pos (div_pos zero_lt_one Real.pi_pos)
    (Real.sqrt_pos.mpr Real.pi_pos)
  have hweights (m : ℕ) (side : Bool) :
      W.T.H (W.T.sample m) ^ (3 / 4 : ℝ) * W.T.E0 (W.T.sample (W.C.cell m)) ^ Ac ≤
        (Cs * Ct) *
          (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
            W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (Pt + 1)) := by
    have h₁ := hshift m (W.C.cell m) (W.T.sample (W.C.cell m)) (hs _)
      ((abs_sub_comm _ _).trans_le (hindex m))
    have h₂ : W.T.H (W.T.sample (W.C.cell m)) ^ (3 / 4 : ℝ) *
        W.T.E0 (W.T.sample (W.C.cell m)) ^ Ps ≤
      Ct * (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
        W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ Pt) := by
      simpa only [Real.rpow_zero, mul_one] using
        hhost (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
          (W.C.cell m) (W.host m)
    have hH : 0 ≤ W.T.H
        (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg (W.hT.2.1 _
        (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
    calc
      _ ≤ Cs * (W.T.H (W.T.sample (W.C.cell m)) ^ (3 / 4 : ℝ) *
          W.T.E0 (W.T.sample (W.C.cell m)) ^ Ps) := by simpa only [mul_assoc] using h₁
      _ ≤ Cs * (Ct *
          (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
            W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ Pt)) :=
        mul_le_mul_of_nonneg_left h₂ hCs.le
      _ ≤ Cs * (Ct *
          (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
            W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (Pt + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (W.floor _) (by linarith)) hH) hCt.le) hCs.le
      _ = _ := by ring
  refine ⟨c * Bc * Cs * Ct, Pt + 1,
    mul_pos (mul_pos (mul_pos hc hBc) hCs) hCt, by linarith only [hPt], ?_⟩
  intro m side t ht v
  have htfull : t ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) :=
    ⟨ht.1, ht.2.trans (W.negativeOpticalWidth_le_component m side)⟩
  have hk := abs_stateKappa_le_weight_mul_stateGrading W.hS W.hT W.radial.1 v 0 m
  have hv : 0 ≤ stateGrading W.S 0 v := apply_nonneg _ _
  rw [abs_mul]
  calc
    _ ≤ (stateKappaSeminormWeight W.T m * stateGrading W.S 0 v) *
        (Bc * W.T.E0 (W.T.sample (W.C.cell m)) ^ Ac) :=
      mul_le_mul hk (hcontrol m side t htfull) (abs_nonneg _)
        (mul_nonneg (stateKappaSeminormWeight_nonneg W.hT W.radial.1 m) hv)
    _ = (c * Bc) *
        (W.T.H (W.T.sample m) ^ (3 / 4 : ℝ) * W.T.E0 (W.T.sample (W.C.cell m)) ^ Ac) *
          stateGrading W.S 0 v := by dsimp only [stateKappaSeminormWeight, c]; ring
    _ ≤ (c * Bc) * ((Cs * Ct) *
        (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
          W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (Pt + 1))) *
            stateGrading W.S 0 v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hweights m side) (mul_pos hc hBc).le) hv
    _ = _ := by ring

/-- The ordinary spatial square jets have sampled coefficient cost on
the fixed neighborhood. The direction estimate above remains separate. -/
theorem stateSquare_material_jets (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2), ∀ m side t,
        t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
          |iteratedDeriv n (F.stateSquare z m side) t| ≤
            B * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ A := by
  obtain ⟨Cr, hCr, hr⟩ := F.reference_powers 1
  obtain ⟨Cd, Ad, hCd, hAd, hd⟩ := F.control_direction_material_jets n
  obtain ⟨M, hM, hweight⟩ := materialHeight_E0_weight_bounded W.hT
    (γ := (3 / 4 : ℝ)) (by norm_num) Ad
  let Q : ℝ := 1 + stateGrading W.S 0 W.C.referenceState + W.ε
  have hQ : 0 < Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (stateGrading W.S 0) W.C.referenceState, W.ε_pos]
  refine ⟨Cr n + Cd * M * Q, Cr n,
    add_pos (hCr n) (mul_pos (mul_pos hCd hM) hQ), hCr n, ?_⟩
  intro z hz m side t ht
  let E := W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side)))))
  have hE : 1 ≤ E := W.floor _
  have href : |iteratedDeriv n (F.reference m side) t| ≤ Cr n * E ^ (Cr n) := by
    simpa only [Real.rpow_one] using hr m side t ht n
  have hzQ : stateGrading W.S 0 z.1 ≤ Q := by
    have hb := stateGrading_zero_le_reference_add_radius hz
    dsimp only [Q]
    linarith only [hb, W.ε_pos]
  have hdir : |stateKappa W.S z.1 m * iteratedDeriv n (F.control m side) t| ≤ Cd * M * Q := by
    have hw := hweight (W.T.sample ((W.A e).cell (e.symm (.inl (m, side)))))
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)
    calc
      _ ≤ (Cd * (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ) *
          E ^ Ad)) * stateGrading W.S 0 z.1 := by
        simpa only [mul_assoc] using hd m side t ht z.1
      _ ≤ (Cd * M) * Q := mul_le_mul
        (mul_le_mul_of_nonneg_left hw hCd.le) hzQ (apply_nonneg _ _) (mul_pos hCd hM).le
  change |iteratedDeriv n
    (fun x => F.reference m side x - stateKappa W.S z.1 m * F.control m side x) t| ≤ _
  rw [iteratedDeriv_fun_sub ((F.reference_smooth m side).contDiffAt.of_le (by simp))
    ((contDiff_const.mul (F.control_smooth m side)).contDiffAt.of_le (by simp)),
    iteratedDeriv_const_mul_field]
  calc
    _ ≤ |iteratedDeriv n (F.reference m side) t| +
        |stateKappa W.S z.1 m * iteratedDeriv n (F.control m side) t| := abs_sub _ _
    _ ≤ Cr n * E ^ (Cr n) + Cd * M * Q := add_le_add href hdir
    _ ≤ Cr n * E ^ (Cr n) + (Cd * M * Q) * E ^ (Cr n) :=
      add_le_add le_rfl (le_mul_of_one_le_right (mul_pos (mul_pos hCd hM) hQ).le
        (Real.one_le_rpow hE (hCr n).le))
    _ = _ := by ring

end ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.control_direction_material_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.control_direction_material_jets
