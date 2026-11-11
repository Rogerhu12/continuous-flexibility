import ContinuousFlexibility.Radial.MorseChainScales
import ContinuousFlexibility.Radial.MorseCellMassTravel

/-!
# Basic consequences of an arbitrary realized Morse chain

These projections use the frozen realization itself, rather than the
stronger witness used to construct one particular chain. Enlarging its
positive constants preserves every quantitative clause.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Real
open scoped ContDiff Topology

theorem AccumulatingProfileBounds.mono {D : ReferenceData} {C C' : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) (hCC : ∀ s, C s ≤ C' s) :
    AccumulatingProfileBounds D C' := by
  rcases h with ⟨hgeom, hpart, hC, hne, hfinite, hlocal, hdist, hlow, hjet,
    hinv, hwidth, hscale, htrace⟩
  have hC' (s : ℕ) : 0 < C' s := (hC s).trans_le (hCC s)
  have hInv : (C' 0)⁻¹ ≤ (C 0)⁻¹ := inv_anti₀ (hC 0) (hCC 0)
  refine ⟨hgeom, hpart, hC', hne, hfinite, hlocal, ?_, ?_, ?_, ?_, ?_, hscale, htrace⟩
  · intro m r hr
    obtain ⟨hl, hu⟩ := hdist m r hr
    exact ⟨(mul_le_mul_of_nonneg_right hInv (exp_pos _).le).trans hl,
      hu.trans (mul_le_mul_of_nonneg_right (hCC 0) (exp_pos _).le)⟩
  · intro m r hr
    have hp := mul_le_mul_of_nonneg_right (hCC 0) (sq_nonneg (D.cellIndex m : ℝ))
    exact (exp_le_exp.mpr (by linarith only [hp])).trans (hlow m r hr)
  · intro m r hr s
    have hp := mul_le_mul_of_nonneg_right (hCC s) (sq_nonneg (D.cellIndex m : ℝ))
    exact (hjet m r hr s).trans (mul_le_mul (hCC s)
      (exp_le_exp.mpr (by linarith only [hp])) (exp_pos _).le (hC' s).le)
  · intro m r hr s
    have hE : 1 ≤ radialE (D.cellIndex m) :=
      one_le_exp_iff.mpr ((sq_nonneg (D.cellIndex m : ℝ)).trans
        (Radial.radial_nat_sq_le_Q (D.cellIndex m)))
    exact (hinv m r hr s).trans (mul_le_mul (hCC s)
      (Real.rpow_le_rpow_of_exponent_le hE (hCC s))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (hC' s).le)
  · intro m
    obtain ⟨l, r, hsub, hlen⟩ := hwidth m
    exact ⟨l, r, hsub, hlen.trans
      (mul_le_mul_of_nonneg_right (hCC 0) (exp_pos _).le)⟩

namespace MorseChainRealization

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}

theorem accumulating (h : MorseChainRealization T σ D C) : AccumulatingProfileBounds D C := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hAcc⟩
  exact hAcc

theorem geometry (h : MorseChainRealization T σ D C) : RadialProfileGeometry D :=
  h.accumulating.1

theorem constants_pos (h : MorseChainRealization T σ D C) (s : ℕ) : 0 < C s :=
  h.accumulating.2.2.1 s

theorem retained_data (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    0 < morseChainB T n ∧ 4 * morseChainB T n < morseChainA T n ∧
    T.leftX side n = -log (3 / 2) ∧
    T.leftX side n < morseChainRightTurn T n ∧
    morseChainRightTurn T n < T.rightX side n ∧
    T.rightX side n = morseChainRightTurn T n + (1 / 100 : ℝ) / morseChainA T n ^ 4 ∧
    deriv (T.radius side n) (morseChainRightTurn T n) =
      (1 / 100 : ℝ) * morseChainA T n ^ 5 * T.radius side n (morseChainRightTurn T n) :=
  h.2.1 side n hn

theorem radius_smooth (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) : ContDiff ℝ ∞ (T.radius side n) :=
  (h.2.2.1 side n hn).1

theorem derivative_positive (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (X : ℝ)
    (hX : X ∈ Icc (T.leftX side n) (T.rightX side n)) :
    0 < deriv (T.radius side n) X :=
  ((h.2.2.1 side n hn).2.2 X hX).1

theorem equation (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (X : ℝ)
    (hX : X ∈ Icc (T.leftX side n) (T.rightX side n)) :
    deriv (deriv (T.radius side n)) X =
      -Radial.morseRho (morseChainA T n) (morseChainB T n) X * T.radius side n X :=
  ((h.2.2.1 side n hn).2.2 X hX).2.1

theorem profile_eq (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (X : ℝ)
    (hX : X ∈ Icc (T.leftX side n) (T.rightX side n)) :
    D.w (T.radius side n X) = morseChainAmplitude T σ n * deriv (T.radius side n) X :=
  ((h.2.2.1 side n hn).2.2 X hX).2.2

theorem radius_mem_core (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (X : ℝ)
    (hX : X ∈ Icc (T.leftX side n) (T.rightX side n)) :
    T.radius side n X ∈ radialCore D :=
  h.2.2.2.2.1 side n hn ⟨X, hX, rfl⟩

theorem radius_positive (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (X : ℝ)
    (hX : X ∈ Icc (T.leftX side n) (T.rightX side n)) :
    0 < T.radius side n X :=
  h.geometry.1.trans (h.radius_mem_core side n hn X hX).1

theorem radius_strictMonoOn (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    StrictMonoOn (T.radius side n) (Icc (T.leftX side n) (T.rightX side n)) :=
  Radial.morseCell_strictMonoOn (h.radius_smooth side n hn) (h.derivative_positive side n hn)

theorem join_data (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    T.joinLeft side n < T.joinRight side n ∧
    T.joinLeft side n = (if side then T.radius side n (T.rightX side n)
      else T.radius side (n + 1) (T.rightX side (n + 1))) ∧
    T.joinRight side n = (if side then T.radius side (n + 1) (T.leftX side (n + 1))
      else T.radius side n (T.leftX side n)) ∧
    T.joinRight side n - T.joinLeft side n ≤ C 0 * (morseChainA T n) ^ 12 ∧
    ∀ r ∈ Ioo (T.joinLeft side n) (T.joinRight side n),
      2 / r ≤ deriv D.w r / D.w r :=
  h.2.2.2.1 side n hn

theorem d_eq (h : MorseChainRealization T σ D C) (n : ℕ) (hn : T.index ≤ n) :
    T.d n = Radial.morseChainInteger n := by
  have hd := h.1 n hn
  have hs := Radial.morseChainInteger_spec n
  rcases lt_trichotomy (T.d n) (Radial.morseChainInteger n) with hlt | heq | hgt
  · exact False.elim (hd.2.1 (Radial.morseChainInteger_minimal n (T.d n) hd.1 hlt))
  · exact heq
  · exact False.elim (hs.2 (hd.2.2 _ hs.1 hgt))

theorem mono {C' : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (hCC : ∀ s, C s ≤ C' s) : MorseChainRealization T σ D C' := by
  rcases h with ⟨hd, hret, hmodel, hjoin, hinside, hmiddle, hlimits, hlocal, hcover, hAcc⟩
  refine ⟨hd, hret, hmodel, ?_, hinside, hmiddle, hlimits, hlocal, hcover, hAcc.mono hCC⟩
  intro side n hn
  obtain ⟨hlr, hl, hr, hwidth, hslope⟩ := hjoin side n hn
  have hA : 0 ≤ morseChainA T n := sq_nonneg _
  exact ⟨hlr, hl, hr, hwidth.trans
    (mul_le_mul_of_nonneg_right (hCC 0) (pow_nonneg hA 12)), hslope⟩

end MorseChainRealization

end ContinuousFlexibility.Statements
