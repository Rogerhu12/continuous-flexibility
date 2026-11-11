import ContinuousFlexibility.Radial.OuterFullCore
import ContinuousFlexibility.Radial.OuterCoreMassScale

/-!
# Hilbert mass of the complete transition core

The outgoing right connector is a subinterval of the next ordinary
core.  Its already proved mass bound and the adjacent amplitude ratio
therefore include it without assuming a separate mass estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

def outerCoreMassPrefactor (D₀ D : ReferenceData) (C : ℕ → ℝ) (K : ℝ) : ℝ :=
  (12 / D.a ^ 8) *
    (K * (9 ^ 2 + 9 ^ 6) + (C 0 * K * D₀.b ^ 6 * exp 300) * 9 ^ 6)

theorem radialHilbertIntervalMass_mono {D : ReferenceData} {l r s t : ℝ}
    (hD : RadialProfileGeometry D) (hlr : l ≤ r) (hsub : Icc l r ⊆ radialCore D)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    radialHilbertIntervalMass D s t ≤ radialHilbertIntervalMass D l r := by
  have hf : ContinuousOn (fun x => 12 * D.w x / x ^ 2) (Icc l r) :=
    (continuousOn_const.mul hD.2.2.1.1.continuous.continuousOn).div
      (continuousOn_id.pow 2)
      (fun x hx => (pow_pos (hD.1.trans (hsub hx).1) 2).ne')
  have hf₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ 12 * D.w x / x ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (hD.2.2.2.2.1 x (hsub hx)).le) (sq_nonneg x)
  exact (le_abs_self _).trans (outer_abs_integral_le_whole hlr hf hf₀ hs ht)

theorem morseOuterFullCore_mass_le_height_exp {T : MorseChainData} {σ : ℕ → ℝ}
    {D₀ D : ReferenceData} {C : ℕ → ℝ} {K : ℝ}
    (h₀ : MorseChainRealization T (fun _ => 1) D₀ C)
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : T.index < n) :
    radialHilbertIntervalMass D (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n) ≤
      (2 * outerCoreMassPrefactor D₀ D C K) * morseChainAmplitude T σ n * exp (135 * (n : ℝ) ^ 2) := by
  let M := outerCoreMassPrefactor D₀ D C K
  let lam := morseChainAmplitude T σ n
  let N := (n : ℝ) ^ 2
  let B := M * lam * exp (135 * N)
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have hM : 0 ≤ M := by dsimp only [M, outerCoreMassPrefactor]; positivity
  have hlam : 0 < lam := morseChainAmplitude_pos T σ hσ n
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hn1 : 1 ≤ n := by omega
  have hN : 0 ≤ N := sq_nonneg _
  have hold : radialHilbertIntervalMass D (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) ≤ B := by
    calc
      _ ≤ M * lam * exp (27 * N) := morseOuterCore_mass_le_height_exp h₀ h hσ hcell side n hn
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith only [hN])) (mul_nonneg hM hlam.le)
  cases side with
  | false =>
      calc
        _ ≤ B := hold
        _ ≤ 2 * B := by linarith only [hB]
        _ = _ := by dsimp only [B, M, lam, N]; ring
  | true =>
      have hj := h.join_data true n hn.le
      have hseam : T.joinLeft true n = morseOuterCoreRight T true n := by
        simpa only [morseOuterCoreRight, ite_true] using hj.2.1
      have hnext : T.index < n + 1 := by omega
      have hnextCore := morseOuterCore_interval h true (n + 1) hnext
      have hnextPieces := (morseOuterCore_contains_pieces h true (n + 1) hnext).2
      simp only [Nat.add_sub_cancel] at hnextPieces
      have hjoinNext : radialHilbertIntervalMass D (T.joinLeft true n) (T.joinRight true n) ≤
          radialHilbertIntervalMass D (morseOuterCoreLeft T true (n + 1)) (morseOuterCoreRight T true (n + 1)) :=
        radialHilbertIntervalMass_mono h.geometry hnextCore.1.le hnextCore.2
          (hnextPieces (left_mem_Icc.mpr hj.1.le)) (hnextPieces (right_mem_Icc.mpr hj.1.le))
      have hratio := morseAdjacentScale_amplitude_le_exp_sq T σ hσ hn1 hn.le hnext.le (Or.inl rfl)
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hnextsq : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * N := by
        dsimp only [N]
        push_cast
        nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
      have hjoin : radialHilbertIntervalMass D (T.joinLeft true n) (T.joinRight true n) ≤ B := by
        calc
          _ ≤ radialHilbertIntervalMass D (morseOuterCoreLeft T true (n + 1))
              (morseOuterCoreRight T true (n + 1)) := hjoinNext
          _ ≤ M * morseChainAmplitude T σ (n + 1) * exp (27 * ((n + 1 : ℕ) : ℝ) ^ 2) :=
            morseOuterCore_mass_le_height_exp h₀ h hσ hcell true (n + 1) hnext
          _ ≤ M * (lam * exp (27 * N)) * exp (108 * N) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hratio hM)
              (exp_le_exp.mpr (by nlinarith only [hnextsq])) (exp_pos _).le (by positivity)
          _ = M * lam * (exp (27 * N) * exp (108 * N)) := by ring
          _ = B := by
            dsimp only [B]
            rw [← exp_add]
            congr 2
            ring
      have hc := morseOuterCore_interval h true n hn
      have hf := morseOuterFullCore_interval h true n hn
      have hsplit : radialHilbertIntervalMass D (morseOuterCoreLeft T true n) (morseOuterFullCoreRight T true n) =
          radialHilbertIntervalMass D (morseOuterCoreLeft T true n) (morseOuterCoreRight T true n) +
            radialHilbertIntervalMass D (morseOuterCoreRight T true n) (morseOuterFullCoreRight T true n) :=
        radialHilbertIntervalMass_add h.geometry
          (hc.2 (left_mem_Icc.mpr hc.1.le)) (hc.2 (right_mem_Icc.mpr hc.1.le))
          (hf.2 (right_mem_Icc.mpr hf.1.le))
      calc
        _ = radialHilbertIntervalMass D (morseOuterCoreLeft T true n) (morseOuterCoreRight T true n) +
            radialHilbertIntervalMass D (T.joinLeft true n) (T.joinRight true n) := by
          rw [hsplit, hseam]
        _ ≤ B + B := add_le_add hold hjoin
        _ = _ := by dsimp only [B, M, lam, N]; ring

theorem morseOuterFullCore_mass_le_state_scale {T : MorseChainData} {σ : ℕ → ℝ}
    {D₀ D : ReferenceData} {C : ℕ → ℝ} {K scale L : ℝ}
    (h₀ : MorseChainRealization T (fun _ => 1) D₀ C)
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : T.index < n) (hScalePos : 0 < scale)
    (hscale : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    radialHilbertIntervalMass D (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n) ≤
      scale * exp ((L + 135 + 2 * outerCoreMassPrefactor D₀ D C K) * (n : ℝ) ^ 2) := by
  let M := 2 * outerCoreMassPrefactor D₀ D C K
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have hM : 0 ≤ M := by dsimp only [M, outerCoreMassPrefactor]; positivity
  have hpref : M ≤ exp (M * (n : ℝ) ^ 2) := nonneg_le_exp_mul_nat_sq hM (by omega)
  have hlam : morseChainAmplitude T σ n ≤ scale * exp (L * (n : ℝ) ^ 2) :=
    ((div_le_iff₀ hScalePos).mp hscale).trans_eq (mul_comm _ _)
  calc
    _ ≤ M * morseChainAmplitude T σ n * exp (135 * (n : ℝ) ^ 2) :=
      morseOuterFullCore_mass_le_height_exp h₀ h hσ hcell side n hn
    _ ≤ (exp (M * (n : ℝ) ^ 2) * (scale * exp (L * (n : ℝ) ^ 2))) *
        exp (135 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hpref hlam (morseChainAmplitude_pos T σ hσ n).le (exp_pos _).le) (exp_pos _).le
    _ = _ := by
      rw [mul_left_comm (exp (M * (n : ℝ) ^ 2)) scale, mul_assoc, ← exp_add, ← exp_add]
      congr 2
      dsimp only [M]
      ring

end ContinuousFlexibility.Radial
