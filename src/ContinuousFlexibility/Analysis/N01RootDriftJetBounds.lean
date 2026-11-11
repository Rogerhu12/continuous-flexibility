import ContinuousFlexibility.Analysis.N01RootCoefficientValueRectangle
import ContinuousFlexibility.Analysis.N01ShiftedCoefficientJets
import ContinuousFlexibility.Analysis.PositiveDenominatorQuotientBounds

/-!
# Actual fixed-loss mixed jets of the oriented characteristic drift

The scalar compatibility identity is a·d=b. The actual radial coefficient
has a state-independent positive value range. On one additional common
low-seminorm ball, the zeroth coefficient estimate bounds b as well.
One genuine quotient composition therefore controls the drift at every
spatial order. The orientation ±1 does not change absolute mixed jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n01_orientedCharacteristicDrift_fixed_loss_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ r σ : ℝ, ∀ g : ℝ → ℝ, ∀ R : ℝ,
      (σ = 1 ∨ σ = -1) → 0 < R → ContDiff ℝ ∞ g →
      Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b →
      ∀ m : ℕ, Ioo (r - R) (r + R) ⊆ D.cells m →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ R) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ a b : ℕ, ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        |mixedDerivative a b
          (orientedCharacteristicDrift (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) q| ≤
          B (a + b) * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
            (z - (C.referenceState, 0))) := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation p :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨lowQ, outLoss, hquotient⟩ := quotient_fixed_loss_bound hp hI loss
  refine ⟨max lowQ loss, outLoss, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip
  have hphysicalInner : Ioo (r - R) (r + R) ⊆ Ioo D.a D.b := by
    intro x hx
    apply hphysical
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨A, hA, hAbound⟩ :=
    shiftedOriginalCoefficient_fixed_loss_bound_of_n01 hS hT hN hσ hR hphysical m hcell
  obtain ⟨l₁, u₁, l₂, u₂, _, h₂, _, hlu₂, hrectangle⟩ :=
    n01_rootCoefficient_positive_value_rectangle hS hT hN hσ hR hg hphysicalInner hstrip
  obtain ⟨B, hB, hbound⟩ := hquotient A hA (-(2 * A 0)) (2 * A 0) l₂ u₂ h₂ hlu₂
  refine ⟨B, hB, ?_⟩
  intro z hz hsector hlow
  let x : AnnularState S × ℝ := z - (C.referenceState, 0)
  have hlowQ : p lowQ x ≤ 1 := (hp (Nat.le_max_left lowQ loss) x).trans hlow
  have hlowLoss : p loss x ≤ 1 := (hp (Nat.le_max_right lowQ loss) x).trans hlow
  let U : Set PolarPoint := Ioo (-R) R ×ˢ (univ : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let u : PolarPoint → ℝ := fun q =>
    canonicalCoefficientComponent 1 (originalCoefficients D S C z) (rootProfileShift r σ q)
  let v : PolarPoint → ℝ := fun q =>
    canonicalCoefficientComponent 0 (originalCoefficients D S C z) (rootProfileShift r σ q)
  have hu : ContDiffOn ℝ ∞ u U :=
    contDiffOn_shiftedOriginalCoefficient_of_n01 hS hT hN hσ hphysicalInner hz hsector 1
  have hv : ContDiffOn ℝ ∞ v U :=
    contDiffOn_shiftedOriginalCoefficient_of_n01 hS hT hN hσ hphysicalInner hz hsector 0
  have hnum (q : PolarPoint) (hq : q ∈ U) : |u q| ≤ 2 * A 0 := by
    have hh : |u q| ≤ A 0 * (1 + p loss x) := by
      simpa only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] using
        hAbound 0 z hz hsector 1 0 0 le_rfl q hq
    have hm := mul_le_mul_of_nonneg_left
      (show 1 + p loss x ≤ 2 by linarith) (zero_le_one.trans (hA 0))
    exact hh.trans (by simpa only [mul_comm] using hm)
  have hrange (q : PolarPoint) (hq : q ∈ U) :
      (u q, v q) ∈ Icc (-(2 * A 0)) (2 * A 0) ×ˢ Icc l₂ u₂ :=
    ⟨abs_le.mp (hnum q hq), (hrectangle z hz hsector q hq).2⟩
  have hujet (q : PolarPoint) (hq : q ∈ U) (a b : ℕ) :
      |mixedDerivative a b u q| ≤ A (a + b) * (1 + p (a + b + loss) x) :=
    hAbound (a + b) z hz hsector 1 a b le_rfl q hq
  have hvjet (q : PolarPoint) (hq : q ∈ U) (a b : ℕ) :
      |mixedDerivative a b v q| ≤ A (a + b) * (1 + p (a + b + loss) x) :=
    hAbound (a + b) z hz hsector 0 a b le_rfl q hq
  have he : EqOn (fun q => u q / v q)
      (fun q => characteristicDrift (stateProfile D S C z.1)
        (stateHeight D S C z) (rootProfileShift r σ q)) U := by
    intro q hq
    have hpouter : q ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hq.1.1, hq.1.2]
    obtain ⟨hrq, _, _, _, hQq, _, _⟩ := hstrip z hz hsector q hpouter
    have hva : 0 < v q := h₂.trans_le (hrange q hq).2.1
    have hh := polarLinearA_mul_characteristicDrift
      ((contDiff_stateHeight_of_n01 hS hT hN z).contDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞))
      hrq.ne' hQq.ne'
    change v q * characteristicDrift (stateProfile D S C z.1)
      (stateHeight D S C z) (rootProfileShift r σ q) = u q at hh
    exact (div_eq_iff hva.ne').mpr (hh.symm.trans (mul_comm _ _))
  have hsign : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  intro a b q hq
  have hh := hbound x hlowQ U hU u v hu hv hrange hujet hvjet a b q hq
  have hj := mixedDerivative_eqOn_of_isOpen hU he a b hq
  have hraw := (congrArg abs hj).symm.trans_le hh
  change |mixedDerivative a b (fun y => σ *
    characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z)
      (rootProfileShift r σ y)) q| ≤ _
  rw [spaces_mixedDerivative_const_mul, abs_mul, hsign, one_mul]
  exact hraw

end ContinuousFlexibility.Analysis
