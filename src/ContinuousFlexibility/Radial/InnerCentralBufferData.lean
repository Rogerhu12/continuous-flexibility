module

public import ContinuousFlexibility.Radial.InnerCentralModelBorder
public import ContinuousFlexibility.Radial.InnerCentralCapScale

/-!
# Actual central buffer data at every even frequency

The same two far cuts, layer constant and full-model inverse constant
work for all positive even modes. Only the second mode carries the
genuine compact temporary border. All compression hypotheses below
are proved from the actual quadratic potential and the spectral inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

def innerCentralBufferData (n : ℕ) (X₀ : ℝ) : BufferData where
  bordered := decide (n = 1)
  potential := centralPotential (2 * n)
  border := if n = 1 then innerCentralModelBorder else 0
  l := -X₀
  h := X₀
  mass := fun _ => innerCentralCapMass (2 * n) X₀
  action := fun _ => innerCentralCapAction (2 * n) X₀
  B₀ := innerCentralModelInverseConstant
  layerBound := 64 + 16 * centralRadiusA ^ 2
  borderFunction := if n = 1 then innerCentralModelBorderFunction else 0

def innerCentralBufferRadius (n : ℕ) (X₀ : ℝ) : ℝ :=
  X₀ - (innerCentralCapAction (2 * n) X₀ + 6) / innerCentralCapMass (2 * n) X₀

theorem innerCentralBuffer_frequency {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ≤ 2 * n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith only [hn']

theorem innerCentralCapMass_ge_four {j X₀ : ℝ} (hj : 2 ≤ j) (hX : 8 ≤ X₀) :
    4 ≤ innerCentralCapMass j X₀ := by
  have hm : (2 : ℝ) * 8 ≤ j * X₀ :=
    mul_le_mul hj hX (by norm_num) (by linarith)
  unfold innerCentralCapMass
  linarith only [hm]

theorem innerCentralBufferRadius_bounds {n : ℕ} (hn : 1 ≤ n)
    {X₀ : ℝ} (hX : 8 ≤ X₀) :
    X₀ / 2 ≤ innerCentralBufferRadius n X₀ ∧ innerCentralBufferRadius n X₀ ≤ X₀ := by
  have hj := innerCentralBuffer_frequency hn
  have hm := innerCentralCapMass_pos (by linarith : (0 : ℝ) < 2 * n)
    (by linarith : 0 < X₀)
  have haction := innerCentralCapAction_pos (by linarith : (0 : ℝ) < 2 * n)
    (by linarith : 0 < X₀)
  have hfit := innerCentralCap_buffer_fits hj hX
  have hnonneg := div_nonneg (show 0 ≤ innerCentralCapAction (2 * n) X₀ + 6 by linarith)
    hm.le
  unfold innerCentralBufferRadius
  constructor <;> linarith only [hfit, hnonneg]

theorem innerCentralBufferCut (n : ℕ) (X₀ : ℝ) (i : Fin 2) :
    bufferCut (innerCentralBufferData n X₀) i = bufferSign i * X₀ := by
  unfold bufferCut bufferSign innerCentralBufferData
  split_ifs <;> ring

theorem innerCentralBufferInnerWall (n : ℕ) (X₀ : ℝ) (i : Fin 2) :
    bufferInnerWall (innerCentralBufferData n X₀) i =
      bufferSign i * innerCentralBufferRadius n X₀ := by
  rw [bufferInnerWall, innerCentralBufferCut]
  dsimp only [innerCentralBufferData, innerCentralBufferRadius]
  ring

theorem innerCentralBufferBorder_ae (n : ℕ) (X₀ : ℝ) :
    ((innerCentralBufferData n X₀).border : ℝ → ℝ) =ᵐ[volume]
      (innerCentralBufferData n X₀).borderFunction := by
  by_cases hn : n = 1
  · simpa only [innerCentralBufferData, if_pos hn] using innerCentralModelBorder_ae
  · simpa only [innerCentralBufferData, if_neg hn] using (Lp.coeFn_zero ℝ 2 volume)

theorem innerCentralBufferBorder_support (n : ℕ) (X₀ : ℝ) :
    Function.support (innerCentralBufferData n X₀).borderFunction ⊆
      Icc (-innerCentralModelBorderRadius) innerCentralModelBorderRadius := by
  by_cases hn : n = 1
  · simpa only [innerCentralBufferData, if_pos hn] using
      (show Function.support innerCentralModelBorderFunction ⊆ tsupport innerCentralModelBorderFunction
        from subset_closure).trans innerCentralModelBorderFunction_tsupport
  · simp only [innerCentralBufferData, if_neg hn, Function.support_zero, empty_subset]

/-- Both kinds of local upper-bound layers stay in the same quadratic
scale. The proof uses the distance to either center only once. -/
theorem innerCentralBuffer_layer_abs {n : ℕ} (hn : 1 ≤ n) {X₀ : ℝ} (hX : 8 ≤ X₀)
    (i : Fin 2) {x : ℝ}
    (hx : |x - bufferCut (innerCentralBufferData n X₀) i| ≤
        4 / (innerCentralBufferData n X₀).mass i ∨
      |x - bufferInnerWall (innerCentralBufferData n X₀) i| ≤
        4 / (innerCentralBufferData n X₀).mass i) : |x| ≤ 2 * X₀ := by
  have hj := innerCentralBuffer_frequency hn
  have hr := innerCentralBufferRadius_bounds hn hX
  have hρ : 0 ≤ innerCentralBufferRadius n X₀ := (by linarith : 0 ≤ X₀ / 2).trans hr.1
  have hcut : |bufferCut (innerCentralBufferData n X₀) i| ≤ X₀ := by
    rw [innerCentralBufferCut, abs_mul, abs_bufferSign, one_mul,
      abs_of_nonneg (by linarith : 0 ≤ X₀)]
  have hwall : |bufferInnerWall (innerCentralBufferData n X₀) i| ≤ X₀ := by
    rw [innerCentralBufferInnerWall, abs_mul, abs_bufferSign, one_mul, abs_of_nonneg hρ]
    exact hr.2
  have hm4 := innerCentralCapMass_ge_four hj hX
  have hstep : 4 / (innerCentralBufferData n X₀).mass i ≤ 1 := by
    apply (div_le_iff₀ (show 0 < innerCentralCapMass (2 * n) X₀ by linarith)).mpr
    simpa only [one_mul] using hm4
  obtain ⟨c, hxc, hc⟩ : ∃ c : ℝ,
      |x - c| ≤ 4 / (innerCentralBufferData n X₀).mass i ∧ |c| ≤ X₀ := by
    rcases hx with hx | hx
    · exact ⟨bufferCut (innerCentralBufferData n X₀) i, hx, hcut⟩
    · exact ⟨bufferInnerWall (innerCentralBufferData n X₀) i, hx, hwall⟩
  calc
    |x| = |(x - c) + c| := by rw [sub_add_cancel]
    _ ≤ |x - c| + |c| := abs_add_le _ _
    _ ≤ 1 + X₀ := add_le_add (hxc.trans hstep) hc
    _ ≤ 2 * X₀ := by linarith only [hX]

/-- Every hypothesis of the frozen compression theorem follows for
the actual central family, including its full arbitrary-source inverse. -/
theorem innerCentralBufferData_hypotheses {n : ℕ} (hn : 1 ≤ n)
    {X₀ : ℝ} (hX : 8 ≤ X₀) (hfar : 8 * centralOscillatorA ≤ X₀ ^ 2)
    (hsupportCut : 2 * (innerCentralModelBorderRadius + 1) ≤ X₀) :
    BufferHypotheses (innerCentralBufferData n X₀) := by
  have hj := innerCentralBuffer_frequency hn
  have hj0 : (0 : ℝ) < 2 * n := by linarith only [hj]
  have hX0 : 0 < X₀ := by linarith only [hX]
  have hm := innerCentralCapMass_pos hj0 hX0
  have ha := innerCentralCapAction_pos hj0 hX0
  have hρ := innerCentralBufferRadius_bounds hn hX
  have hs0 : bufferSign (0 : Fin 2) = -1 := rfl
  have hs1 : bufferSign (1 : Fin 2) = 1 := rfl
  have hwalls : bufferInnerWall (innerCentralBufferData n X₀) 0 <
      bufferInnerWall (innerCentralBufferData n X₀) 1 := by
    rw [innerCentralBufferInnerWall, innerCentralBufferInnerWall, hs0, hs1,
      neg_one_mul, one_mul]
    linarith only [hρ.1, hX0]
  have hborder : ContDiff ℝ ∞ (innerCentralBufferData n X₀).borderFunction ∧
      HasCompactSupport (innerCentralBufferData n X₀).borderFunction := by
    by_cases hn1 : n = 1
    · simpa only [innerCentralBufferData, if_pos hn1] using
        And.intro contDiff_innerCentralModelBorderFunction
          innerCentralModelBorderFunction_hasCompactSupport
    · have hzero : (fun _ : ℝ => (0 : ℝ)) = (0 : ℝ → ℝ) := by
        funext x
        simp only [Pi.zero_apply]
      simpa only [innerCentralBufferData, if_neg hn1, hzero] using
        (And.intro (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
          (HasCompactSupport.zero : HasCompactSupport (fun _ : ℝ => (0 : ℝ))))
  refine ⟨(by dsimp only [innerCentralBufferData]; linarith only [hX0]), hwalls,
    innerCentralModelInverseConstant_pos, ?_, ?_, centralActualClosedFormRealization hj0,
    hborder.1, hborder.2, innerCentralBufferBorder_ae n X₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [innerCentralBufferData]
    positivity
  · change ContDiff ℝ ∞ (centralPotential (2 * n))
    unfold centralPotential
    fun_prop
  · intro x hx
    have hxs := innerCentralBufferBorder_support n X₀ hx
    rw [innerCentralBufferInnerWall, innerCentralBufferInnerWall, hs0, hs1,
      neg_one_mul, one_mul]
    exact ⟨by linarith only [hxs.1, hρ.1, hsupportCut],
      by linarith only [hxs.2, hρ.1, hsupportCut]⟩
  · intro i
    exact ⟨hm, ha⟩
  · apply (ae_restrict_iff' measurableSet_Ioo.compl).mpr
    filter_upwards [innerCentralBufferBorder_ae n X₀] with x hx
    intro hout
    rw [hx]
    by_contra hne
    have hxs := innerCentralBufferBorder_support n X₀ hne
    exact hout ⟨by dsimp only [innerCentralBufferData]; linarith only [hxs.1, hX, hsupportCut],
      by dsimp only [innerCentralBufferData]; linarith only [hxs.2, hX, hsupportCut]⟩
  · intro i x hx
    change innerCentralCapMass (2 * n) X₀ ^ 2 ≤ centralPotential (2 * n) x
    apply innerCentralCap_potential_lower hX0.le hfar
    by_cases hi : i = 0
    · simp only [hi, ite_true, innerCentralBufferData] at hx
      have hxρ : innerCentralBufferRadius n X₀ ≤ -x := by
        dsimp only [innerCentralBufferRadius]
        linarith only [hx]
      exact hρ.1.trans (hxρ.trans (neg_le_abs x))
    · simp only [hi, ite_false, innerCentralBufferData] at hx
      exact hρ.1.trans (hx.trans (le_abs_self x))
  · intro i x hx
    exact innerCentralCap_potential_upper ((by norm_num : (1 : ℝ) ≤ 2).trans hj)
      ((by norm_num : (1 : ℝ) ≤ 8).trans hX) (innerCentralBuffer_layer_abs hn hX i hx)
  · exact exists_innerCentralModelFullInverse n hn

/-- The one fixed physical auxiliary source only adds a fixed support
floor to the far-cut choice. Every later enlargement is still allowed. -/
theorem exists_innerCentralBufferCut (C initial : ℝ) :
    ∃ X₀ : ℝ, initial ≤ X₀ ∧ 8 ≤ X₀ ∧
      (∀ n : ℕ, 1 ≤ n → BufferHypotheses (innerCentralBufferData n X₀)) ∧
      (∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ innerCentralCapMass j X₀) := by
  obtain ⟨X₀, hinit, h8, hfar, hmass⟩ := exists_innerCentral_far_cut C
    (max initial (2 * (innerCentralModelBorderRadius + 1)))
  have hs : 2 * (innerCentralModelBorderRadius + 1) ≤ X₀ :=
    (le_max_right _ _).trans hinit
  exact ⟨X₀, (le_max_left _ _).trans hinit, h8,
    fun n hn => innerCentralBufferData_hypotheses hn h8 hfar hs, hmass⟩

/-- The central action grows linearly in frequency with a coefficient
chosen before the tail realization. -/
theorem innerCentralBuffer_action (n : ℕ) (X₀ : ℝ) (i : Fin 2) :
    (innerCentralBufferData n X₀).action i = (X₀ ^ 2 / 16) * (2 * n) := by
  dsimp only [innerCentralBufferData, innerCentralCapAction]
  ring

/-- The actual central velocity bound is uniform over the cut interval. -/
theorem innerCentralBuffer_velocity {X₀ : ℝ}
    {x : ℝ} (hx : x ∈ Icc (-X₀) X₀) :
    |deriv centralRadius x / centralRadius x| ≤ centralRadiusWeightConstant * (1 + X₀) := by
  have h := centralRadiusLogDerivative_norm_le_linear x
  have habs : |x| ≤ X₀ := abs_le.mpr hx
  exact (show |deriv centralRadius x / centralRadius x| ≤
    centralRadiusWeightConstant * (1 + |x|) by
      simpa only [centralRadiusLogDerivative, Real.norm_eq_abs] using h).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) habs) centralRadiusWeightConstant_pos.le)

end ContinuousFlexibility.Radial
