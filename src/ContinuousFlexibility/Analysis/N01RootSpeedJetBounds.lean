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

/-- The complete composition estimate over an abstract state space. -/
private def RootSpeedRecoveryBound
    {E : Type} [AddCommGroup E] [Module ℝ E] (p : ℕ → Seminorm ℝ E)
    (lowH low lossH loss outLoss : ℕ) (AH : ℕ → ℕ → ℝ) (Aa B : ℕ → ℝ)
    (l₁ u₁ l₂ u₂ : ℝ) : Prop :=
  ∀ x : E, p low x ≤ 1 → ∀ U : Set PolarPoint, IsOpen U →
    ∀ u v f : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U →
      (∀ q ∈ U, (u q, v q) ∈ Icc l₁ u₁ ×ˢ Icc l₂ u₂) →
      (p lowH x ≤ 1 → ∀ q ∈ U, ∀ a b : ℕ,
        |mixedDerivative a b u q| ≤ AH a b * (1 + p (a + b + lossH) x)) →
      (∀ q ∈ U, ∀ a b : ℕ,
        |mixedDerivative a b v q| ≤ Aa (a + b) * (1 + p (a + b + loss) x)) →
      EqOn (fun q => Real.sqrt (u q) / v q) f U →
      ∀ a b : ℕ, ∀ q ∈ U, |mixedDerivative a b f q| ≤
        B (a + b) * (1 + p (a + b + outLoss) x)

/-- Choose the common low order and loss before either input majorant
or the positive value rectangle. All grade arithmetic is abstract. -/
private theorem rootSpeedRecovery_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (lowH lossH loss : ℕ) :
    ∃ low outLoss : ℕ, ∀ AH : ℕ → ℕ → ℝ, (∀ a b, 0 < AH a b) →
      ∀ Aa : ℕ → ℝ, (∀ n, 1 ≤ Aa n) →
      ∀ l₁ u₁ l₂ u₂ : ℝ, 0 < l₁ → 0 < l₂ → l₁ ≤ u₁ → l₂ ≤ u₂ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        RootSpeedRecoveryBound p lowH low lossH loss outLoss AH Aa B l₁ u₁ l₂ u₂ := by
  let inputLoss := max loss lossH
  obtain ⟨lowC, outLoss, hrecover⟩ := sqrtQuotient_fixed_loss_bound hp hI inputLoss
  refine ⟨max lowH lowC, outLoss, ?_⟩
  intro AH hAH Aa hAa l₁ u₁ l₂ u₂ h₁ h₂ hlu₁ hlu₂
  obtain ⟨A, hA, hAaA, hAHA⟩ := exists_common_split_jet_majorant Aa AH hAa hAH
  obtain ⟨B, hB, hbound⟩ := hrecover A hA l₁ u₁ l₂ u₂ h₁ h₂ hlu₁ hlu₂
  refine ⟨B, hB, ?_⟩
  intro x hlow U hU u v f hu hv hrange hHjet hAjet he a b q hq
  have hlowH : p lowH x ≤ 1 := (hp (Nat.le_max_left lowH lowC) x).trans hlow
  have hlowC : p lowC x ≤ 1 := (hp (Nat.le_max_right lowH lowC) x).trans hlow
  have hujet (y : PolarPoint) (hy : y ∈ U) (i j : ℕ) :
      |mixedDerivative i j u y| ≤ A (i + j) * (1 + p (i + j + inputLoss) x) := by
    have hhigher : 1 + p (i + j + lossH) x ≤ 1 + p (i + j + inputLoss) x :=
      add_le_add (le_refl (1 : ℝ))
        (hp (Nat.add_le_add_left (Nat.le_max_right loss lossH) (i + j)) x)
    exact (hHjet hlowH y hy i j).trans (mul_le_mul (hAHA i j) hhigher
      (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans (hA (i + j))))
  have hvjet (y : PolarPoint) (hy : y ∈ U) (i j : ℕ) :
      |mixedDerivative i j v y| ≤ A (i + j) * (1 + p (i + j + inputLoss) x) := by
    have hhigher : 1 + p (i + j + loss) x ≤ 1 + p (i + j + inputLoss) x :=
      add_le_add (le_refl (1 : ℝ))
        (hp (Nat.add_le_add_left (Nat.le_max_left loss lossH) (i + j)) x)
    exact (hAjet y hy i j).trans (mul_le_mul (hAaA (i + j)) hhigher
      (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans (hA (i + j))))
  have hh := hbound x hlowC U hU u v hu hv hrange hujet hvjet a b q hq
  have hj := mixedDerivative_eqOn_of_isOpen hU he a b hq
  exact (congrArg abs hj).symm.trans_le hh

/-- Exactly the original complete state- and point-wise speed estimate. -/
def N01FactoredSpeedBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε r σ : ℝ) (g : ℝ → ℝ) (R : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ a b : ℕ, ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
      |mixedDerivative a b
        (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ) q| ≤
        B (a + b) * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
          (z - (C.referenceState, 0)))

/-- Genuine smoothness of the two inputs and their actual square-root
identity are independent of the representation of the state. -/
private theorem rootSpeed_recovery_compatibility
    {wref g w : ℝ → ℝ} {Z : PolarPoint → ℝ} {r σ R : ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hZ : ContDiff ℝ ∞ Z) (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions wref g w Z r σ R) :
    ContDiffOn ℝ ∞ (rootCoefficientRadialFactor wref g w Z r σ)
        (Ioo (-R) R ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ (fun q => polarLinearA w Z (rootProfileShift r σ q))
        (Ioo (-R) R ×ˢ (univ : Set ℝ)) ∧
      EqOn (fun q => Real.sqrt (rootCoefficientRadialFactor wref g w Z r σ q) /
          polarLinearA w Z (rootProfileShift r σ q))
        (factoredCharacteristicSpeed wref g w Z r σ)
        (Ioo (-R) R ×ˢ (univ : Set ℝ)) := by
  have hpoint (q : PolarPoint) (hq : q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ)) :=
    hstrip q (show q ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hq.1.1, hq.1.2])
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨hrq, hwq, hgq, hDq, hQq, _, _⟩ := hpoint q hq
    exact (contDiffAt_rootCoefficientRadialFactor
      hwref hg hw hZ hrq hwq hgq hDq hQq).contDiffWithinAt
  · intro q hq
    obtain ⟨hrq, _, _, hDq, hQq, _, _⟩ := hpoint q hq
    have hrad := (contDiffAt_heightLinearCoefficients
      hw.contDiffAt hZ.contDiffAt hrq.ne' hDq hQq.ne').1
    exact (hrad.comp q hshift.contDiffAt).contDiffWithinAt
  · intro q hq
    obtain ⟨hrq, hwq, hgq, hDq, hQq, _, _⟩ := hpoint q hq
    exact (factoredCharacteristicSpeed_eq_sqrt_div_coefficient hrq hwq hgq hDq hQq).symm

private theorem n01_shiftedRadialCoefficient_jet_bound
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base loss : ℕ} {ε r σ R : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hlu : r - R ≤ r + R) (hR : 0 < R) (Aa : ℕ → ℝ)
    (hAa : ∀ n, LocalizedOriginalCoefficientBoundAtOrder
      D S C base loss ε hlu hR n (Aa n))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (q : PolarPoint)
    (hq : q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ)) (a b : ℕ) :
    |mixedDerivative a b (fun y => polarLinearA (stateProfile D S C z.1)
        (stateHeight D S C z) (rootProfileShift r σ y)) q| ≤
      Aa (a + b) * (1 + pairGrading (stateGrading S) realGrading (a + b + loss)
        (z - (C.referenceState, 0))) := by
  have hqphysical : rootProfileShift r σ q ∈
      Ioo (r - R) (r + R) ×ˢ (univ : Set ℝ) :=
    ⟨rootProfileShift_mem_symmetric_interval hσ hq.1, mem_univ _⟩
  have he0 : canonicalCoefficientComponent (0 : Fin 3) (originalCoefficients D S C z) =
      polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) := rfl
  have hjet := mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    (localizedOriginalCoefficient_eqOn D S C hlu hR z 0) a b hqphysical
  rw [he0] at hjet
  calc
    _ = |mixedDerivative a b (polarLinearA (stateProfile D S C z.1)
        (stateHeight D S C z)) (rootProfileShift r σ q)| :=
      abs_mixedDerivative_rootProfileShift _ hσ a b q
    _ = |mixedDerivative a b
        (localizedOriginalCoefficient D S C hlu hR z 0) (rootProfileShift r σ q)| :=
      (congrArg abs hjet).symm
    _ ≤ _ := hAa (a + b) z hz hsector 0 a b le_rfl (rootProfileShift r σ q) hqphysical

private theorem n01_factoredSpeed_bound_of_recovery
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss lowH lossH low outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ R l₁ u₁ l₂ u₂ : ℝ} {g : ℝ → ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hR : 0 < R) (hg : ContDiff ℝ ∞ g)
    (hlu : r - R ≤ r + R)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R)
    (AH : ℕ → ℕ → ℝ) (Aa B : ℕ → ℝ)
    (hHbound : ∀ a b, N01RootCoefficientRadialFactorBoundAtOrder
      D S C base lowH lossH ε r σ g R a b (AH a b))
    (hAbound : ∀ n, LocalizedOriginalCoefficientBoundAtOrder
      D S C base loss ε hlu hR n (Aa n))
    (hrectangle : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        (rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ q,
          polarLinearA (stateProfile D S C z.1) (stateHeight D S C z)
            (rootProfileShift r σ q)) ∈ Icc l₁ u₁ ×ˢ Icc l₂ u₂)
    (hbound : RootSpeedRecoveryBound (pairGrading (stateGrading S) realGrading)
      lowH low lossH loss outLoss AH Aa B l₁ u₁ l₂ u₂) :
    N01FactoredSpeedBound D S C base low outLoss ε r σ g R B := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  intro z hz hsector hlow
  have hregular := rootSpeed_recovery_compatibility hwref hg
    (contDiff_stateProfile_of_n01 hS hT hN z.1)
    (contDiff_stateHeight_of_n01 hS hT hN z) hR (hstrip z hz hsector)
  exact hbound (z - (C.referenceState, 0)) hlow
    (Ioo (-R) R ×ˢ (univ : Set ℝ)) (isOpen_Ioo.prod isOpen_univ)
    (rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ)
    (fun q => polarLinearA (stateProfile D S C z.1) (stateHeight D S C z)
      (rootProfileShift r σ q))
    (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ)
    hregular.1 hregular.2.1 (hrectangle z hz hsector)
    (fun hlowH q hq a b => hHbound a b z hz hsector hlowH q hq)
    (fun q hq a b => n01_shiftedRadialCoefficient_jet_bound
      hσ hlu hR Aa hAbound hz hsector q hq a b) hregular.2.2

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
        N01FactoredSpeedBound D S C base low outLoss ε r σ g R B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨lowH, lossH, hfactor⟩ := n01_rootCoefficientRadialFactor_fixed_loss_bound hS hT hN
  obtain ⟨low, outLoss, hrecover⟩ := rootSpeedRecovery_fixed_loss_bound hp hI lowH lossH loss
  refine ⟨low, outLoss, ?_⟩
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
  obtain ⟨l₁, u₁, l₂, u₂, h₁, h₂, hlu₁, hlu₂, hrectangle⟩ :=
    n01_rootCoefficient_positive_value_rectangle hS hT hN hσ hR hg hphysicalInner hstrip
  obtain ⟨B, hB, hbound⟩ := hrecover AH hAH Aa hAa l₁ u₁ l₂ u₂ h₁ h₂ hlu₁ hlu₂
  exact ⟨B, hB, n01_factoredSpeed_bound_of_recovery hS hT hN hσ hR hg hlu
    hstrip AH Aa B hHbound hAbound hrectangle hbound⟩

end ContinuousFlexibility.Analysis
