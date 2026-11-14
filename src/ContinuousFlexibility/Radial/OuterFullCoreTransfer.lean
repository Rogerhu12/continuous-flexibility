module

public import ContinuousFlexibility.Radial.OuterFullCore
public import ContinuousFlexibility.Radial.OuterTransferNorm

/-!
# The actual continuous linear core transfer and its inverse

The coefficient functions are continuous because the complete core is
a compact subinterval of the regular physical annulus.  The transfer
is constructed by solving the actual value/flux system for every
initial state before its operator norm is estimated.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem outerPhysical_coefficients_continuous {D : ReferenceData} {scale l r : ℝ}
    (hD : RadialProfileGeometry D) (hscale : 0 < scale)
    (hsub : Icc l r ⊆ radialCore D) (j : ℝ) :
    ContinuousOn (fun x => scale / D.w x) (Icc l r) ∧
      ContinuousOn (fun x => j ^ 2 * deriv D.w x / (scale * x)) (Icc l r) := by
  have hw := hD.2.2.1.1
  have hd : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hwp (x : ℝ) (hx : x ∈ Icc l r) : 0 < D.w x := hD.2.2.2.2.1 x (hsub hx)
  have hxp (x : ℝ) (hx : x ∈ Icc l r) : 0 < x := hD.1.trans (hsub hx).1
  exact ⟨continuousOn_const.div hw.continuous.continuousOn (fun x hx => (hwp x hx).ne'),
    (continuousOn_const.mul hd.continuousOn).div (continuousOn_const.mul continuousOn_id)
      (fun x hx => (mul_pos hscale (hxp x hx)).ne')⟩

def morseOuterFullCoreTransfer {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {scale : ℝ}
    (h : MorseChainRealization T σ D C) (hscale : 0 < scale)
    (side : Bool) (n : ℕ) (hn : T.index < n) (j : ℝ) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  let hi := morseOuterFullCore_interval h side n hn
  let hc := outerPhysical_coefficients_continuous h.geometry hscale hi.2 j
  outerStateTransfer hi.1.le hc.1 hc.2
    (left_mem_Icc.mpr hi.1.le) (right_mem_Icc.mpr hi.1.le)

theorem morseOuterFullCoreTransfer_actual {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {scale j : ℝ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hscale : 0 < scale)
    (side : Bool) (n : ℕ) (hn : T.index < n)
    (hstate : ∀ r ∈ Icc (morseOuterCoreLeft T side n) (morseOuterFullCoreRight T side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z (j ^ 2 * deriv D.w r / (scale * r) * u r) r) :
    morseOuterFullCoreTransfer h hscale side n hn j
        (u (morseOuterCoreLeft T side n), z (morseOuterCoreLeft T side n)) =
      (u (morseOuterFullCoreRight T side n), z (morseOuterFullCoreRight T side n)) := by
  have hi := morseOuterFullCore_interval h side n hn
  have hc := outerPhysical_coefficients_continuous h.geometry hscale hi.2 j
  exact outerStateTransfer_actual hi.1.le hc.1 hc.2
    (left_mem_Icc.mpr hi.1.le) (right_mem_Icc.mpr hi.1.le) hstate

/-- The sum of the norms of the genuine core solution operator and its
genuine inverse has the manuscript's quadratic/action exponential form. -/
theorem morseOuterFullCoreTransfer_norms_le_of_upper
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale : ℝ} {n j : ℕ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hupper : (j : ℝ) < radialFrequencyThreshold T Cstar n)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    ‖(morseOuterFullCoreTransfer h hscale side n hn (j : ℝ)).toContinuousLinearMap‖ +
        ‖(morseOuterFullCoreTransfer h hscale side n hn (j : ℝ)).symm.toContinuousLinearMap‖ ≤
      exp ((outerFullCoreQuadraticExponent C K D.a Cstar L + 2) * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) := by
  have hi := morseOuterFullCore_interval h side n hn
  have hc := outerPhysical_coefficients_continuous h.geometry hscale hi.2 (j : ℝ)
  have hK : 0 < K := hcell.pos
  have hC : 0 < C 0 := h.constants_pos 0
  have ha : 0 < D.a := h.geometry.1
  have hQ : 0 ≤ outerFullCoreQuadraticExponent C K D.a Cstar L := by
    dsimp only [outerFullCoreQuadraticExponent, outerCoreInteriorQuadraticExponent,
      outerCoreQuadraticExponent, outerOutgoingQuadraticExponent, outerFrequencyExponent, outerJoinPrefactor]
    positivity
  have hτ : 0 ≤ outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n)) := by
    dsimp only [outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  apply outerStateTransfer_norms_le_exp hi.1.le (by omega : 1 ≤ n) hc.1 hc.2
    (left_mem_Icc.mpr hi.1.le) (right_mem_Icc.mpr hi.1.le) hQ hτ
  intro u z hstate
  constructor
  · simpa only [outerStateEnergy, mul_comm] using
      morseOuterFullCore_energy_on_exp_of_upper h hσ hcell hscale hL side hn hupper hhi hlo hstate
        (left_mem_Icc.mpr hi.1.le) (right_mem_Icc.mpr hi.1.le)
  · simpa only [outerStateEnergy, mul_comm] using
      morseOuterFullCore_energy_on_exp_of_upper h hσ hcell hscale hL side hn hupper hhi hlo hstate
        (right_mem_Icc.mpr hi.1.le) (left_mem_Icc.mpr hi.1.le)

theorem morseOuterFullCoreTransfer_norms_le
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale : ℝ} {n j : ℕ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (side : Bool) (hn : T.index < n) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    ‖(morseOuterFullCoreTransfer h hscale side n hn (j : ℝ)).toContinuousLinearMap‖ +
        ‖(morseOuterFullCoreTransfer h hscale side n hn (j : ℝ)).symm.toContinuousLinearMap‖ ≤
      exp ((outerFullCoreQuadraticExponent C K D.a Cstar L + 2) * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) :=
  morseOuterFullCoreTransfer_norms_le_of_upper h hσ hcell hscale hL side hn hband.2.2 hhi hlo

end ContinuousFlexibility.Radial
