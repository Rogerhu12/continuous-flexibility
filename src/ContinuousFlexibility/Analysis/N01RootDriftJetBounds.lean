module

public import ContinuousFlexibility.Analysis.N01RootCoefficientValueRectangle
public import ContinuousFlexibility.Analysis.N01ShiftedCoefficientJets
public import ContinuousFlexibility.Analysis.PositiveDenominatorQuotientBounds

/-!
# Actual fixed-loss mixed jets of the oriented characteristic drift

The scalar compatibility identity is a·d=b. The actual radial coefficient
has a state-independent positive value range. On one additional common
low-seminorm ball, the zeroth coefficient estimate bounds b as well.
One genuine quotient composition therefore controls the drift at every
spatial order. The orientation ±1 does not change absolute mixed jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private def OrientedQuotientBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (inputLoss low outLoss : ℕ)
    (A B : ℕ → ℝ) (l v : ℝ) : Prop :=
  ∀ x : E, p low x ≤ 1 → ∀ U : Set PolarPoint, IsOpen U →
    ∀ u w d : PolarPoint → ℝ, ∀ σ : ℝ, |σ| = 1 →
    ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ w U →
    (∀ q ∈ U, w q ∈ Icc l v) →
    (∀ q ∈ U, ∀ a b : ℕ, |mixedDerivative a b u q| ≤
      A (a + b) * (1 + p (a + b + inputLoss) x)) →
    (∀ q ∈ U, ∀ a b : ℕ, |mixedDerivative a b w q| ≤
      A (a + b) * (1 + p (a + b + inputLoss) x)) →
    (∀ q ∈ U, w q * d q = u q) →
    ∀ a b : ℕ, ∀ q ∈ U,
      |mixedDerivative a b (fun y => σ * d y) q| ≤
        B (a + b) * (1 + p (a + b + outLoss) x)

/-- All quotient arithmetic is performed over an abstract state space. -/
private theorem orientedQuotient_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∀ l v : ℝ, 0 < l → l ≤ v →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        OrientedQuotientBound p inputLoss low outLoss A B l v := by
  obtain ⟨lowQ, outLoss, hquotient⟩ := quotient_fixed_loss_bound hp hI inputLoss
  refine ⟨max lowQ inputLoss, outLoss, ?_⟩
  intro A hA l v hl hlv
  obtain ⟨B, hB, hbound⟩ := hquotient A hA (-(2 * A 0)) (2 * A 0) l v hl hlv
  refine ⟨B, hB, ?_⟩
  intro x hlow U hU u w d σ hσ hu hw hden hujet hwjet hcompat
  have hlowQ : p lowQ x ≤ 1 :=
    (hp (Nat.le_max_left lowQ inputLoss) x).trans hlow
  have hlowLoss : p inputLoss x ≤ 1 :=
    (hp (Nat.le_max_right lowQ inputLoss) x).trans hlow
  have hnum (q : PolarPoint) (hq : q ∈ U) : |u q| ≤ 2 * A 0 := by
    have hh : |u q| ≤ A 0 * (1 + p inputLoss x) := by
      simpa only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] using hujet q hq 0 0
    have hm := mul_le_mul_of_nonneg_left
      (show 1 + p inputLoss x ≤ 2 by linarith) (zero_le_one.trans (hA 0))
    exact hh.trans (by simpa only [mul_comm] using hm)
  have hrange (q : PolarPoint) (hq : q ∈ U) :
      (u q, w q) ∈ Icc (-(2 * A 0)) (2 * A 0) ×ˢ Icc l v :=
    ⟨abs_le.mp (hnum q hq), hden q hq⟩
  have he : EqOn (fun q => u q / w q) d U := by
    intro q hq
    have hwpos : 0 < w q := hl.trans_le (hden q hq).1
    exact (div_eq_iff hwpos.ne').mpr ((hcompat q hq).symm.trans (mul_comm _ _))
  intro a b q hq
  have hh := hbound x hlowQ U hU u w hu hw hrange hujet hwjet a b q hq
  have hj := mixedDerivative_eqOn_of_isOpen hU he a b hq
  rw [spaces_mixedDerivative_const_mul, abs_mul, hσ, one_mul]
  exact (congrArg abs hj).symm.trans_le hh

/-- The complete original state-wise conclusion, named before choosing
the coefficient and quotient constants. -/
def N01OrientedDriftBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε r σ R : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ a b : ℕ, ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
      |mixedDerivative a b
        (orientedCharacteristicDrift (stateProfile D S C z.1)
          (stateHeight D S C z) r σ) q| ≤
        B (a + b) * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
          (z - (C.referenceState, 0)))

private theorem n01_shifted_characteristicDrift_compatibility
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ R : ℝ} {g : ℝ → ℝ} (hR : 0 < R) (z : AnnularState S × ℝ)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ R)
    {q : PolarPoint} (hq : q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ)) :
    canonicalCoefficientComponent 0 (originalCoefficients D S C z) (rootProfileShift r σ q) *
        characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z)
          (rootProfileShift r σ q) =
      canonicalCoefficientComponent 1 (originalCoefficients D S C z)
        (rootProfileShift r σ q) := by
  have hpouter : q ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hq.1.1, hq.1.2]
  obtain ⟨hrq, _, _, _, hQq, _, _⟩ := hstrip q hpouter
  exact polarLinearA_mul_characteristicDrift
    ((contDiff_stateHeight_of_n01 hS hT hN z).contDiffAt.of_le
      (by simp : (2 : ℕ∞ω) ≤ ∞)) hrq.ne' hQq.ne'

private theorem n01_orientedDrift_bound_of_quotient
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss low outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ R l v : ℝ} {g : ℝ → ℝ} (hσ : σ = 1 ∨ σ = -1) (hR : 0 < R)
    (hphysical : Ioo (r - R) (r + R) ⊆ Ioo D.a D.b)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R)
    (A B : ℕ → ℝ)
    (hA : ∀ s : ℕ, ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        |mixedDerivative a b
          (fun y => canonicalCoefficientComponent i (originalCoefficients D S C z)
            (rootProfileShift r σ y)) q| ≤
          A s * (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0))))
    (hden : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        polarLinearA (stateProfile D S C z.1) (stateHeight D S C z)
          (rootProfileShift r σ q) ∈ Icc l v)
    (hbound : OrientedQuotientBound (pairGrading (stateGrading S) realGrading)
      loss low outLoss A B l v) :
    N01OrientedDriftBound D S C base low outLoss ε r σ R B := by
  intro z hz hsector hlow
  have hsign : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  exact hbound (z - (C.referenceState, 0)) hlow
    (Ioo (-R) R ×ˢ (univ : Set ℝ)) (isOpen_Ioo.prod isOpen_univ)
    (fun q => canonicalCoefficientComponent 1 (originalCoefficients D S C z)
      (rootProfileShift r σ q))
    (fun q => canonicalCoefficientComponent 0 (originalCoefficients D S C z)
      (rootProfileShift r σ q))
    (fun q => characteristicDrift (stateProfile D S C z.1)
      (stateHeight D S C z) (rootProfileShift r σ q)) σ hsign
    (contDiffOn_shiftedOriginalCoefficient_of_n01 hS hT hN hσ hphysical hz hsector 1)
    (contDiffOn_shiftedOriginalCoefficient_of_n01 hS hT hN hσ hphysical hz hsector 0)
    (hden z hz hsector)
    (fun q hq a b => hA (a + b) z hz hsector 1 a b le_rfl q hq)
    (fun q hq a b => hA (a + b) z hz hsector 0 a b le_rfl q hq)
    (fun q hq => n01_shifted_characteristicDrift_compatibility hS hT hN hR z
      (hstrip z hz hsector) hq)

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
        N01OrientedDriftBound D S C base low outLoss ε r σ R B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hquotient⟩ := orientedQuotient_fixed_loss_bound hp hI loss
  refine ⟨low, outLoss, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip
  have hphysicalInner : Ioo (r - R) (r + R) ⊆ Ioo D.a D.b := by
    intro x hx
    apply hphysical
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨A, hA, hAbound⟩ :=
    shiftedOriginalCoefficient_fixed_loss_bound_of_n01 hS hT hN hσ hR hphysical m hcell
  obtain ⟨l₁, u₁, l₂, u₂, _, h₂, _, hlu₂, hrectangle⟩ :=
    n01_rootCoefficient_positive_value_rectangle hS hT hN hσ hR hg hphysicalInner hstrip
  obtain ⟨B, hB, hbound⟩ := hquotient A hA l₂ u₂ h₂ hlu₂
  exact ⟨B, hB, n01_orientedDrift_bound_of_quotient hS hT hN hσ hR hphysicalInner
    hstrip A B hAbound (fun z hz hs q hq => (hrectangle z hz hs q hq).2) hbound⟩

end ContinuousFlexibility.Analysis
