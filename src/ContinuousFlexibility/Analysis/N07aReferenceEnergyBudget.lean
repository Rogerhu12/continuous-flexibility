import ContinuousFlexibility.Analysis.N07aReferenceBandBudget
import ContinuousFlexibility.Analysis.N07aReferenceSourceBudget
import ContinuousFlexibility.Analysis.N07aReferenceScalarMaps
import ContinuousFlexibility.Analysis.N07aVolumeWeightBounds

/-!
# The actual reference energy source in an outer square-summable budget

Only the fixed N05 order `b` is used.  Its same inverse field, the same
source, and the three original scalar columns give a genuine outer L²
majorant.  The scalar frequencies remain `0,1,0`; their angular factor is
therefore fixed independently of the input band.  The reference potential
is retained as one sampled subpower envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}

local instance n07aReferenceEnergyLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aReferenceEnergyLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aReferenceEnergyUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aReferenceEnergyUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aReferenceEnergyGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aReferenceEnergyGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

theorem n07a_referenceEnergy_outer_budget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : ReferenceJets D T S C L K) (h05 : N05Properties D T S C K V b B)
    (hI : ∀ m, K.left m < K.right m)
    (Col : Fin 3 → V.level (3 / 4 : ℝ) (0 - B.lossMaterial) 0)
    (hCol : ∀ i, V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) 0 (Col i) =
      fun m => (n07aReferenceScalarOpenCoefficient href m (hI m) i).toLp) :
    ∃ A : ℝ, 0 < A ∧ ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 1 ≤ e m) ∧
      ∀ j (F : V.level (3 / 4 : ℝ) 0 b),
      n07aAngularLevelBand h05.2.1 (3 / 4 : ℝ) 0 hI b j F = F →
      n07aAngularUnknownBand hI j (B.inverse F).val.1 = (B.inverse F).val.1 →
      ∃ a : lp (fun _ : ℕ => ℝ) 2, (∀ m, 0 ≤ a m) ∧ ‖a‖ ≤ A * ‖F‖ ∧
        ∀ m, Real.sqrt (n07aAngularJetWeightSq b j) *
          (‖n07aReferenceInverseField (B := B) F m‖ +
            ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
              (V.forget (3 / 4 : ℝ) 0 b F)‖) ≤
          e m * n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m * a m := by
  obtain ⟨A₀, hA₀, hbound⟩ := n07a_referenceInverse_baseVolume_budget hD hT h05 hI
  obtain ⟨Q, hQ, hq⟩ := n07a_referencePotential_mul_norm href
  let k : ℝ := Real.sqrt (n07aAngularJetWeightSq b 1)
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  let C₀ : ℝ := 1 + ‖Col 0‖ + k * ‖Col 1‖ + ‖Col 2‖
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  let e : ℕ → ℝ := fun m => 1 + Q * T.E0 (T.sample (K.cell m)) ^ Q
  have he : N07aSampleSubpower T K e :=
    (N07aSampleSubpower.const hD hT 1).add
      (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT Q)
        (N07aSampleSubpower.e0_rpow hD hT Q))
  have hq0 (m : ℕ) : 0 ≤ Q * T.E0 (T.sample (K.cell m)) ^ Q := by
    have hE := (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.2.1
    exact mul_nonneg hQ.le (Real.rpow_pos_of_pos hE Q).le
  have he1 (m : ℕ) : 1 ≤ e m := le_add_of_nonneg_right (hq0 m)
  refine ⟨C₀ * A₀ + 1, by positivity, e, he, he1, fun j F hF hU => ?_⟩
  obtain ⟨W, hW, hnorm, hpieces⟩ := hbound F
  let U : CanonicalUnknown S K := (B.inverse F).val.1
  let a : lp (fun _ : ℕ => ℝ) 2 :=
    lp.toNorm W.val + lp.toNorm F.val +
      |U.2.1| • lp.toNorm (Col 0).val +
      (k * |U.2.2.1|) • lp.toNorm (Col 1).val +
      |U.2.2.2| • lp.toNorm (Col 2).val
  have happly (m : ℕ) : a m = ‖W.val m‖ + ‖F.val m‖ +
      |U.2.1| * ‖(Col 0).val m‖ + k * |U.2.2.1| * ‖(Col 1).val m‖ +
      |U.2.2.2| * ‖(Col 2).val m‖ := by
    simp only [a, lp.coeFn_add, lp.coeFn_smul, lp.toNorm_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have ha0 (m : ℕ) : 0 ≤ a m := by rw [happly]; positivity
  have hanorm : ‖a‖ ≤ C₀ * (‖W‖ + canonicalUnknownScalars S K U) + ‖F‖ := by
    have hc1 : 1 ≤ C₀ := by
      dsimp only [C₀]
      linarith [norm_nonneg (Col 0), mul_nonneg hk (norm_nonneg (Col 1)), norm_nonneg (Col 2)]
    have hc0 : ‖Col 0‖ ≤ C₀ := by
      dsimp only [C₀]
      linarith [mul_nonneg hk (norm_nonneg (Col 1)), norm_nonneg (Col 2)]
    have hcμ : k * ‖Col 1‖ ≤ C₀ := by
      dsimp only [C₀]
      linarith [norm_nonneg (Col 0), norm_nonneg (Col 2)]
    have hcλ : ‖Col 2‖ ≤ C₀ := by
      dsimp only [C₀]
      linarith [norm_nonneg (Col 0), mul_nonneg hk (norm_nonneg (Col 1))]
    calc
      ‖a‖ ≤ ‖lp.toNorm W.val‖ + ‖lp.toNorm F.val‖ +
          ‖|U.2.1| • lp.toNorm (Col 0).val‖ +
          ‖(k * |U.2.2.1|) • lp.toNorm (Col 1).val‖ +
          ‖|U.2.2.2| • lp.toNorm (Col 2).val‖ := by
        exact (norm_add_le _ _).trans (add_le_add_right
          ((norm_add_le _ _).trans (add_le_add_right
            ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)) _)) _)
      _ = ‖W‖ + ‖F‖ + |U.2.1| * ‖Col 0‖ +
          |U.2.2.1| * (k * ‖Col 1‖) + |U.2.2.2| * ‖Col 2‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_abs,
          abs_of_nonneg (mul_nonneg hk (abs_nonneg _)), lp.norm_toNorm,
          Submodule.norm_coe]
        ring
      _ ≤ C₀ * (‖W‖ + canonicalUnknownScalars S K U) + ‖F‖ := by
        have hw := mul_le_mul_of_nonneg_right hc1 (norm_nonneg W)
        have h0 := mul_le_mul_of_nonneg_left hc0 (abs_nonneg U.2.1)
        have h1 := mul_le_mul_of_nonneg_left hcμ (abs_nonneg U.2.2.1)
        have h2 := mul_le_mul_of_nonneg_left hcλ (abs_nonneg U.2.2.2)
        dsimp only [canonicalUnknownScalars]
        nlinarith
  refine ⟨a, ha0, hanorm.trans ?_, fun m => ?_⟩
  · have h := mul_le_mul_of_nonneg_left hnorm hC₀.le
    nlinarith
  · let w := n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m
    let q := Q * T.E0 (T.sample (K.cell m)) ^ Q
    let J := Real.sqrt (n07aAngularJetWeightSq b j)
    have hw : 0 ≤ w := (n07aVolumeWeight_pos hD hT _ _ m).le
    have hJ : 0 ≤ J := Real.sqrt_nonneg _
    have huBand : n07aAngularBand m (hI m) j (U.1 m) = U.1 m := by
      simpa only [n07aAngularUnknownBand_field] using
        congrArg (fun u : CanonicalUnknown S K => u.1 m) hU
    have hu : J * ‖U.1 m‖ ≤ w * ‖W.val m‖ := by
      have h := hpieces m j
      rw [huBand] at h
      exact h
    have hfBand : n07aAngularBand m (hI m) j (V.forget (3 / 4 : ℝ) 0 b F m) =
        V.forget (3 / 4 : ℝ) 0 b F m := by
      have h := congrFun (n07aAngularLevelBand_forget h05.2.1 (3 / 4 : ℝ) 0 hI b j F) m
      rw [hF] at h
      exact h.symm
    have hf : J * ‖V.forget (3 / 4 : ℝ) 0 b F m‖ ≤ w * ‖F.val m‖ := by
      have h := n07aVolume_band_piece_norm_le hD hT h05.2.1 (3 / 4 : ℝ) 0 hI b j F m
      rw [hfBand] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (n07aVolumeWeight_antitone hD hT (3 / 4 : ℝ)
          (sub_nonpos.mpr h05.2.2.2.2.1) m) (norm_nonneg _))
    have hc (i : Fin 3) : ‖(n07aReferenceScalarOpenCoefficient href m (hI m) i).toLp‖ ≤
        w * ‖(Col i).val m‖ := by
      have h := n07aVolume_forget_norm_le hD hT h05.2.1 (Col i) m
      rw [hCol i] at h
      exact h
    have hleft : J * |U.2.1| = |U.2.1| := by
      by_cases hj : 0 = j
      · subst j
        simp only [J, n07aAngularJetWeightSq_zero_frequency, Real.sqrt_one, one_mul]
      · have h := congrArg (fun u : CanonicalUnknown S K => u.2.1) hU
        simp only [n07aAngularUnknownBand_left, if_neg hj] at h
        rw [← h, abs_zero, mul_zero]
    have hmiddle : J * |U.2.2.1| = k * |U.2.2.1| := by
      by_cases hj : 1 = j
      · subst j
        rfl
      · have h := congrArg (fun u : CanonicalUnknown S K => u.2.2.1) hU
        simp only [n07aAngularUnknownBand_border, if_neg hj] at h
        rw [← h, abs_zero, mul_zero, mul_zero]
    have hright : J * |U.2.2.2| = |U.2.2.2| := by
      by_cases hj : 0 = j
      · subst j
        simp only [J, n07aAngularJetWeightSq_zero_frequency, Real.sqrt_one, one_mul]
      · have h := congrArg (fun u : CanonicalUnknown S K => u.2.2.2) hU
        simp only [n07aAngularUnknownBand_auxiliary, if_neg hj] at h
        rw [← h, abs_zero, mul_zero]
    have hG := n07aReferenceCanonicalRhs_norm href m (hI m) U
      (V.forget (3 / 4 : ℝ) 0 b F) (hq m (hI m) (U.1 m))
    have h0 := mul_le_mul_of_nonneg_left (hc 0) (abs_nonneg U.2.1)
    have h1 := mul_le_mul_of_nonneg_left (hc 1) (mul_nonneg hk (abs_nonneg U.2.2.1))
    have h2 := mul_le_mul_of_nonneg_left (hc 2) (abs_nonneg U.2.2.2)
    have hqU := mul_le_mul_of_nonneg_left hu (hq0 m)
    have hGJ := mul_le_mul_of_nonneg_left hG hJ
    simp only [mul_add, ← mul_assoc, hleft, hmiddle, hright] at hGJ
    rw [happly]
    have hqw := mul_nonneg (hq0 m) hw
    have hqF := mul_nonneg hqw (norm_nonneg (F.val m))
    have hq0' := mul_nonneg hqw (mul_nonneg (abs_nonneg U.2.1) (norm_nonneg ((Col 0).val m)))
    have hq1' := mul_nonneg hqw
      (mul_nonneg (mul_nonneg hk (abs_nonneg U.2.2.1)) (norm_nonneg ((Col 1).val m)))
    have hq2' := mul_nonneg hqw
      (mul_nonneg (abs_nonneg U.2.2.2) (norm_nonneg ((Col 2).val m)))
    change J * (‖U.1 m‖ + ‖n07aReferenceCanonicalRhs href m (hI m) U
      (V.forget (3 / 4 : ℝ) 0 b F)‖) ≤ _
    dsimp only [e]
    nlinarith

end ContinuousFlexibility.Analysis
