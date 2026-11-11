import ContinuousFlexibility.Analysis.N01RootFactorJetBounds
import ContinuousFlexibility.Analysis.N01RootCoefficientValueRectangle
import ContinuousFlexibility.Analysis.PositiveRootRecoveryBounds

/-!
# Actual fixed-loss mixed jets of the normalized root characteristic speed

The input is the original N01 coefficient estimate, the genuine common
root strip, and its containment in an actual physical cell. Quadratic
interpolation and true division give the divided determinant. The actual
N01 value rectangle then permits one smooth square-root/quotient
composition. No derivative estimate for the resulting root speed is an
input. The common low order and loss precede every root and spatial order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem exists_common_split_jet_majorant
    (A : ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (hA : ∀ n, 1 ≤ A n) (hB : ∀ a b, 0 < B a b) :
    ∃ C : ℕ → ℝ, (∀ n, 1 ≤ C n) ∧ (∀ n, A n ≤ C n) ∧
      ∀ a b, B a b ≤ C (a + b) := by
  let C : ℕ → ℝ := fun n => 1 + A n + ∑ i : Fin (n + 1), B i (n - i)
  have hsum (n : ℕ) : 0 ≤ ∑ i : Fin (n + 1), B i (n - i) :=
    Finset.sum_nonneg (fun i _ => (hB i (n - i)).le)
  refine ⟨C, ?_, ?_, ?_⟩
  · intro n
    dsimp only [C]
    linarith [hA n, hsum n]
  · intro n
    dsimp only [C]
    linarith [hsum n]
  · intro a b
    have hi : a < a + b + 1 := by omega
    have hterm := Finset.single_le_sum
      (f := fun i : Fin (a + b + 1) => B i (a + b - i))
      (fun i _ => (hB i (a + b - i)).le) (Finset.mem_univ (⟨a, hi⟩ : Fin (a + b + 1)))
    have hsub : a + b - a = b := by omega
    have ht : B a b ≤ ∑ i : Fin (a + b + 1), B i (a + b - i) := by
      simpa only [hsub] using hterm
    dsimp only [C]
    linarith [hA (a + b)]

theorem n01_factoredCharacteristicSpeed_fixed_loss_bound
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
          (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
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
  obtain ⟨lowH, lossH, hfactor⟩ := n01_rootCoefficientRadialFactor_fixed_loss_bound hS hT hN
  let inputLoss := max loss lossH
  obtain ⟨lowC, outLoss, hrecover⟩ := sqrtQuotient_fixed_loss_bound hp hI inputLoss
  refine ⟨max lowH lowC, outLoss, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip
  have hlu : r - R ≤ r + R := by linarith
  have hphysicalInner : Ioo (r - R) (r + R) ⊆ Ioo D.a D.b := by
    intro x hx
    apply hphysical
    constructor <;> linarith [hx.1, hx.2]
  choose AH hAH hHbound using
    (fun a b => hfactor r σ g R hσ hR hg hphysical m hcell hstrip a b)
  choose Aa hAa hAbound using
    (fun n => localizedOriginalCoefficient_fixed_loss_bound_of_n01
      hS hT hN hlu hR hphysical m hcell n)
  obtain ⟨A, hA, hAaA, hAHA⟩ := exists_common_split_jet_majorant Aa AH hAa hAH
  obtain ⟨l₁, u₁, l₂, u₂, h₁, h₂, hlu₁, hlu₂, hrectangle⟩ :=
    n01_rootCoefficient_positive_value_rectangle hS hT hN hσ hR hg hphysicalInner hstrip
  obtain ⟨B, hB, hbound⟩ := hrecover A hA l₁ u₁ l₂ u₂ h₁ h₂ hlu₁ hlu₂
  refine ⟨B, hB, ?_⟩
  intro z hz hsector hlow
  let x : AnnularState S × ℝ := z - (C.referenceState, 0)
  have hlowH : p lowH x ≤ 1 := (hp (Nat.le_max_left lowH lowC) x).trans hlow
  have hlowC : p lowC x ≤ 1 := (hp (Nat.le_max_right lowH lowC) x).trans hlow
  let U : Set PolarPoint := Ioo (-R) R ×ˢ (univ : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let u := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  let v : PolarPoint → ℝ := fun q =>
    polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) (rootProfileShift r σ q)
  have hpoint (q : PolarPoint) (hq : q ∈ U) :=
    hstrip z hz hsector q (show q ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hq.1.1, hq.1.2])
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hZ := contDiff_stateHeight_of_n01 hS hT hN z
  have hu : ContDiffOn ℝ ∞ u U := by
    intro q hq
    obtain ⟨hrq, hwq, hgq, hDq, hQq, _, _⟩ := hpoint q hq
    exact (contDiffAt_rootCoefficientRadialFactor
      hwref hg hw hZ hrq hwq hgq hDq hQq).contDiffWithinAt
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hv : ContDiffOn ℝ ∞ v U := by
    intro q hq
    obtain ⟨hrq, _, _, hDq, hQq, _, _⟩ := hpoint q hq
    have hrad := (contDiffAt_heightLinearCoefficients
      hw.contDiffAt hZ.contDiffAt hrq.ne' hDq hQq.ne').1
    exact (hrad.comp q hshift.contDiffAt).contDiffWithinAt
  have hujet (q : PolarPoint) (hq : q ∈ U) (a b : ℕ) :
      |mixedDerivative a b u q| ≤ A (a + b) * (1 + p (a + b + inputLoss) x) := by
    have hh := hHbound a b z hz hsector hlowH q hq
    have hhigher : 1 + p (a + b + lossH) x ≤ 1 + p (a + b + inputLoss) x :=
      add_le_add_left (hp (Nat.add_le_add_left (Nat.le_max_right loss lossH) (a + b)) x) 1
    exact hh.trans (mul_le_mul (hAHA a b) hhigher
      (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans (hA (a + b))))
  have hvjet (q : PolarPoint) (hq : q ∈ U) (a b : ℕ) :
      |mixedDerivative a b v q| ≤ A (a + b) * (1 + p (a + b + inputLoss) x) := by
    have hqphysical : rootProfileShift r σ q ∈
        Ioo (r - R) (r + R) ×ˢ (univ : Set ℝ) :=
      ⟨rootProfileShift_mem_symmetric_interval hσ hq.1, mem_univ _⟩
    have he0 : canonicalCoefficientComponent (0 : Fin 3) (originalCoefficients D S C z) =
        polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) := rfl
    have hjet := mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
      (localizedOriginalCoefficient_eqOn D S C hlu hR z 0) a b hqphysical
    rw [he0] at hjet
    have hhigher : 1 + p (a + b + loss) x ≤ 1 + p (a + b + inputLoss) x :=
      add_le_add_left (hp (Nat.add_le_add_left (Nat.le_max_left loss lossH) (a + b)) x) 1
    calc
      |mixedDerivative a b v q| =
          |mixedDerivative a b (polarLinearA (stateProfile D S C z.1)
            (stateHeight D S C z)) (rootProfileShift r σ q)| :=
        abs_mixedDerivative_rootProfileShift _ hσ a b q
      _ = |mixedDerivative a b
          (localizedOriginalCoefficient D S C hlu hR z 0) (rootProfileShift r σ q)| :=
        (congrArg abs hjet).symm
      _ ≤ Aa (a + b) * (1 + p (a + b + loss) x) :=
        hAbound (a + b) z hz hsector 0 a b le_rfl (rootProfileShift r σ q) hqphysical
      _ ≤ _ := mul_le_mul (hAaA (a + b)) hhigher
        (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans (hA (a + b)))
  have he : EqOn (fun y => Real.sqrt (u y) / v y)
      (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ) U := by
    intro q hq
    obtain ⟨hrq, hwq, hgq, hDq, hQq, _, _⟩ := hpoint q hq
    exact (factoredCharacteristicSpeed_eq_sqrt_div_coefficient hrq hwq hgq hDq hQq).symm
  intro a b q hq
  have hh := hbound x hlowC U hU u v hu hv
    (fun y hy => hrectangle z hz hsector y hy) hujet hvjet a b q hq
  have hj := mixedDerivative_eqOn_of_isOpen hU he a b hq
  exact (congrArg abs hj).symm.trans_le hh

end ContinuousFlexibility.Analysis
