import ContinuousFlexibility.Analysis.N06PositiveDividedSymmetry
import ContinuousFlexibility.Analysis.N06PositiveCubicMultipliers

/-!
# Actual positive cubic control from the retained N05 construction

All qualitative fields of the existing cubic control are now obtained
from the original data. The original N04 bound supplies a genuine finite
absolute bound. Its factor `1 + grading + |q|` is kept explicitly: this
does not assert the additional state-linear smallness needed to close N06.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem n06_abs_three_of_sum {v a b c M E R : ℝ}
    (h : |v| + |a| + |b| + |c| ≤ M * E * R) :
    |a| ≤ (M * R) * E ∧ |b| ≤ (M * R) * E ∧ |c| ≤ (M * R) * E := by
  have he : M * E * R = (M * R) * E := by ring
  refine ⟨LE.le.trans_eq ?_ he, LE.le.trans_eq ?_ he, LE.le.trans_eq ?_ he⟩ <;>
    linarith only [h, abs_nonneg v, abs_nonneg a, abs_nonneg b, abs_nonneg c]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The original mixed-jet sum gives the three actual divided-coefficient
bounds with precisely its stated absolute state factor. -/
theorem n06_actual_dividedMixedJets_bound
    (h04 : N04Properties D T S C L K base loss ε) (s : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (z : AnnularState S × ℝ),
      z ∈ stateNeighborhood S C base ε → ∀ (m : ℕ) (p : PolarPoint),
      p ∈ canonicalOpen S K m → ∀ a j : ℕ, a + j ≤ s →
        |mixedDerivative a j (K.dividedDifference z m).a p| ≤
          (M * (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)) *
            T.E0 (T.sample (K.cell m)) ^ M ∧
        |mixedDerivative a j (K.dividedDifference z m).b p| ≤
          (M * (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)) *
            T.E0 (T.sample (K.cell m)) ^ M ∧
        |mixedDerivative a j (K.dividedDifference z m).c p| ≤
          (M * (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)) *
            T.E0 (T.sample (K.cell m)) ^ M := by
  have hbound := h04.2.2.1
  let M : ℝ := (hbound s).choose
  have hM : 0 < M := (hbound s).choose_spec.1
  have hjet := (hbound s).choose_spec.2
  refine ⟨M, hM, ?_⟩
  intro z hz m p hp a j haj
  exact n06_abs_three_of_sum
    (v := mixedDerivative a j (K.potential z m) p)
    (a := mixedDerivative a j (K.dividedDifference z m).a p)
    (b := mixedDerivative a j (K.dividedDifference z m).b p)
    (c := mixedDerivative a j (K.dividedDifference z m).c p)
    (M := M) (E := T.E0 (T.sample (K.cell m)) ^ M)
    (R := 1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)
    (hjet z hz m p hp a j haj)

/-- Once the proved principal/divided regularity is available, actual
symmetry and any stated mixed-jet bound fill the exact existing cubic
control. No qualitative coefficient hypothesis remains hidden. -/
theorem n06_actualPositiveCubicControl_of_regular
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (b : ℕ) (scale : ℕ → ℝ) (δ : ℝ)
    (hreg : ∀ w ∈ stateNeighborhood S C base ε, stateSector S w.1 →
      ∀ m, K.positive m = true →
        (ContDiffOn ℝ ∞ (K.coefficients w m).a (canonicalOpen S K m) ∧
          ContDiffOn ℝ ∞ (K.coefficients w m).b (canonicalOpen S K m) ∧
          ContDiffOn ℝ ∞ (K.coefficients w m).c (canonicalOpen S K m)) ∧
        (ContDiffOn ℝ ∞ (K.dividedDifference w m).a (canonicalOpen S K m) ∧
          ContDiffOn ℝ ∞ (K.dividedDifference w m).b (canonicalOpen S K m) ∧
          ContDiffOn ℝ ∞ (K.dividedDifference w m).c (canonicalOpen S K m)))
    (hjets : ∀ m, K.positive m = true → ∀ a j, a + j ≤ b + 1 →
      ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative a j (K.dividedDifference z m).a p| ≤ δ * scale m ∧
        |mixedDerivative a j (K.dividedDifference z m).b p| ≤ δ * scale m ∧
        |mixedDerivative a j (K.dividedDifference z m).c p| ≤ δ * scale m) :
    N06PositiveCubicControl K b scale δ
      (fun m => (K.dividedDifference z m).a)
      (fun m => (K.dividedDifference z m).b)
      (fun m => (K.dividedDifference z m).c) := by
  have href := hreg (C.referenceState, 0) (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1)
  have hp (m : ℕ) (hm : K.positive m = true) (p : PolarPoint)
      (hpm : p ∈ canonicalOpen S K m) :=
    n06_positive_dividedCoefficients_periodicOn hT hS h01 h03 h04 hz hs m hm
      (hreg z hz hs m hm).1 (href m hm).1 hpm
  have hr (m : ℕ) (hm : K.positive m = true) (p : PolarPoint)
      (hpm : p ∈ canonicalOpen S K m) :=
    n06_positive_dividedCoefficients_reflectionOn hT hS h01 h03 h04 hz hs m hm
      (hreg z hz hs m hm).1 (href m hm).1 hpm
  exact ⟨fun m hm => (hreg z hz hs m hm).2.1,
    fun m hm => (hreg z hz hs m hm).2.2.1,
    fun m hm => (hreg z hz hs m hm).2.2.2,
    fun m hm p hpm => (hp m hm p hpm).1,
    fun m hm p hpm => (hp m hm p hpm).2.1,
    fun m hm p hpm => (hp m hm p hpm).2.2,
    fun m hm p hpm => (hr m hm p hpm).1,
    fun m hm p hpm => (hr m hm p hpm).2.1,
    fun m hm p hpm => (hr m hm p hpm).2.2, hjets⟩

/-- All original data give an actual cubic control on the very same
complete N05 graph after one neighbourhood restriction. Its original
absolute state factor is preserved verbatim. -/
theorem n06_exists_actualPositiveCubicControl_through05
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hthrough : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε) :
    ∃ ε' M : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ 0 < M ∧
      NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base ε', stateSector S z.1 →
        N06PositiveCubicControl K b (fun m => T.E0 (T.sample (K.cell m)) ^ M)
          (M * (1 + stateGrading S (b + 1 + loss) (z.1 - C.referenceState) + |z.2|))
          (fun m => (K.dividedDifference z m).a)
          (fun m => (K.dividedDifference z m).b)
          (fun m => (K.dividedDifference z m).c) := by
  have hex := n06_exists_positive_regular_through05
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K)
    (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε) hT hS hthrough
  let ε' : ℝ := hex.choose
  have hε' : 0 < ε' := hex.choose_spec.1
  have hle : ε' ≤ ε := hex.choose_spec.2.1
  have hnew := hex.choose_spec.2.2.1
  have hreg := hex.choose_spec.2.2.2
  have h01 := hnew.1.1.1.1
  have h03 := hnew.1.1.2
  have h04 := hnew.1.2.2.2.2.1
  have hb := n06_actual_dividedMixedJets_bound h04 (b + 1)
  let M : ℝ := hb.choose
  have hM : 0 < M := hb.choose_spec.1
  have hbound := hb.choose_spec.2
  refine ⟨ε', M, hε', hle, hM, hnew, ?_⟩
  intro z hz hs
  apply n06_actualPositiveCubicControl_of_regular hT hS h01 h03 h04 hz hs b _ _ hreg
  intro m hm a j haj p hp
  exact hbound z hz m p hp a j haj

end ContinuousFlexibility.Statements
