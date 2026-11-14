module

public import ContinuousFlexibility.Analysis.N01ScaledDividedFactorJets
public import ContinuousFlexibility.Analysis.N01RootCoefficientValueRectangle
public import ContinuousFlexibility.Analysis.N01ActualRootGeometry
public import ContinuousFlexibility.Analysis.N01RootFieldLocalization

/-!
# A genuine positive divided-factor band for the already selected root scale

The actual radial partition supplies a material cell after the root is
fixed. Only the permitted radial band is shortened; the field, scale,
and chosen flow remain unchanged. The positive divided determinant,
its all-order ordinary jets, and a positive localized-speed lower bound
hold on the same closed band, with constants chosen before every state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N01DividedRootBandBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low loss : ℕ) (ε r σ : ℝ) (g : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) (δ ρ lV uV κ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ q : PolarPoint, q.1 ∈ Icc 0 ρ →
      ContDiffAt ℝ ∞ (rootScaledDividedDiscriminant D S C z g r σ δ) q ∧
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) loss B
          (z - (C.referenceState, 0)) (rootScaledDividedDiscriminant D S C z g r σ δ) q ∧
        rootScaledDividedDiscriminant D S C z g r σ δ q ∈ Icc lV uV ∧
        κ ≤ localizedRootSpeed D S C g r σ hR z (δ * q.1, q.2)

private theorem sqrt_div_lower_of_rectangle
    {V a lV ua : ℝ} (hV : lV ≤ V) (ha : 0 < a) (hau : a ≤ ua) :
    Real.sqrt lV / ua ≤ Real.sqrt V / a := by
  calc
    _ ≤ Real.sqrt V / ua :=
      div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hV) (ha.le.trans hau)
    _ ≤ Real.sqrt V / a :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg V) ha hau

private theorem dividedRoot_scaled_band_membership
    {R R₀ δ ρ : ℝ} (hR : 0 < R) (hR₀ : 0 < R₀) (hδ : 0 < δ)
    (hscale : δ * ρ ≤ R₀ / 2) (hscaleR : δ * ρ ≤ R / 4)
    {q : PolarPoint} (hq : q.1 ∈ Icc 0 ρ) :
    δ * q.1 ∈ Ioo (-R₀) R₀ ∧
      (δ * q.1, q.2) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) ∧
      (δ * q.1, q.2) ∈ Ioo (-(R / 2)) (R / 2) ×ˢ (univ : Set ℝ) := by
  have hnonneg : 0 ≤ δ * q.1 := mul_nonneg hδ.le hq.1
  have hupper : δ * q.1 ≤ R₀ / 2 :=
    (mul_le_mul_of_nonneg_left hq.2 hδ.le).trans hscale
  have hquarter : δ * q.1 ≤ R / 4 :=
    (mul_le_mul_of_nonneg_left hq.2 hδ.le).trans hscaleR
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> linarith only [hR₀, hnonneg, hupper]
  · refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR, hnonneg, hquarter]
  · refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR, hnonneg, hquarter]

private theorem dividedRoot_localizedSpeed_lower
    {wref g w : ℝ → ℝ} {k : PolarPoint → ℝ}
    {r σ R lV uV la ua : ℝ} {p : PolarPoint}
    (hR : 0 < R) (hla : 0 < la)
    (houter : p ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ))
    (hhalf : p ∈ Ioo (-(R / 2)) (R / 2) ×ˢ (univ : Set ℝ))
    (hstrip : RootCoefficientStripConditions wref g w k r σ R)
    (hvalue : (rootCoefficientRadialFactor wref g w k r σ p,
      polarLinearA w k (rootProfileShift r σ p)) ∈ Icc lV uV ×ˢ Icc la ua) :
    Real.sqrt lV / ua ≤
      rootFieldLocalization (factoredCharacteristicSpeed wref g w k r σ) hR p := by
  obtain ⟨hr, hw, hg, hD, hQ, _, _⟩ := hstrip p houter
  have ha : 0 < polarLinearA w k (rootProfileShift r σ p) :=
    hla.trans_le hvalue.2.1
  have hc : Real.sqrt lV / ua ≤ factoredCharacteristicSpeed wref g w k r σ p := by
    rw [factoredCharacteristicSpeed_eq_sqrt_div_coefficient hr hw hg hD hQ]
    exact sqrt_div_lower_of_rectangle hvalue.1.1 ha hvalue.2.2
  exact hc.trans_eq
    (rootFieldLocalization_eqOn (F := factoredCharacteristicSpeed wref g w k r σ)
      hR hhalf).symm

private theorem dividedRootBand_family_of_rectangle
    {Z : Type} {U : Set Z} {sector small : Z → Prop}
    {wref g : ℝ → ℝ} {w : Z → ℝ → ℝ} {k : Z → PolarPoint → ℝ}
    {J₁ J₂ : Z → PolarPoint → Prop}
    {r σ R R₀ δ ρ lV uV la ua : ℝ}
    (hR : 0 < R) (hR₀ : 0 < R₀) (hδ : 0 < δ)
    (hscale : δ * ρ ≤ R₀ / 2) (hscaleR : δ * ρ ≤ R / 4)
    (hla : 0 < la)
    (hstrip : ∀ z ∈ U, sector z →
      RootCoefficientStripConditions wref g (w z) (k z) r σ R)
    (hjets : ∀ z ∈ U, sector z → small z → ∀ q : PolarPoint,
      δ * q.1 ∈ Ioo (-R₀) R₀ → J₁ z q ∧ J₂ z q)
    (hvalues : ∀ z ∈ U, sector z →
      ∀ p ∈ Ioo (-R₀) R₀ ×ˢ (univ : Set ℝ),
        (rootCoefficientRadialFactor wref g (w z) (k z) r σ p,
          polarLinearA (w z) (k z) (rootProfileShift r σ p)) ∈
            Icc lV uV ×ˢ Icc la ua) :
    ∀ z ∈ U, sector z → small z → ∀ q : PolarPoint, q.1 ∈ Icc 0 ρ →
      J₁ z q ∧ J₂ z q ∧
        rootCoefficientRadialFactor wref g (w z) (k z) r σ (δ * q.1, q.2) ∈
          Icc lV uV ∧
        Real.sqrt lV / ua ≤ rootFieldLocalization
          (factoredCharacteristicSpeed wref g (w z) (k z) r σ) hR (δ * q.1, q.2) := by
  intro z hz hs hsmall q hq
  obtain ⟨hq₀, houter, hhalf⟩ :=
    dividedRoot_scaled_band_membership hR hR₀ hδ hscale hscaleR hq
  have hvalue := hvalues z hz hs (δ * q.1, q.2) ⟨hq₀, mem_univ _⟩
  have hjet := hjets z hz hs hsmall q hq₀
  exact ⟨hjet.1, hjet.2, hvalue.1,
    dividedRoot_localizedSpeed_lower
      (wref := wref) (g := g) (w := w z) (k := k z) (r := r) (σ := σ)
      hR hla houter hhalf (hstrip z hz hs) hvalue⟩

private theorem n01_dividedRootBand_of_rectangle
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base low loss : ℕ} {ε r σ R R₀ δ ρ lV uV la ua : ℝ} {g : ℝ → ℝ}
    (hR : 0 < R) (hR₀ : 0 < R₀) (hδ : 0 < δ)
    (hscale : δ * ρ ≤ R₀ / 2) (hscaleR : δ * ρ ≤ R / 4)
    (hla : 0 < la)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R)
    (B : ℕ → ℝ)
    (hjets : N01ScaledDividedFactorJetBound D S C base low loss ε r σ g R₀ δ B)
    (hvalues : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ p ∈ Ioo (-R₀) R₀ ×ˢ (univ : Set ℝ),
        (rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ p,
          polarLinearA (stateProfile D S C z.1) (stateHeight D S C z)
            (rootProfileShift r σ p)) ∈ Icc lV uV ×ˢ Icc la ua) :
    N01DividedRootBandBound D S C base low loss ε r σ g hR δ ρ lV uV
      (Real.sqrt lV / ua) B := by
  exact dividedRootBand_family_of_rectangle
    (Z := AnnularState S × ℝ) (U := stateNeighborhood S C base ε)
    (sector := fun z => stateSector S z.1)
    (small := fun z =>
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1)
    (wref := D.w) (g := g) (w := fun z => stateProfile D S C z.1)
    (k := fun z => stateHeight D S C z)
    (J₁ := fun z q =>
      ContDiffAt ℝ ∞ (rootScaledDividedDiscriminant D S C z g r σ δ) q)
    (J₂ := fun z q =>
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) loss B
        (z - (C.referenceState, 0)) (rootScaledDividedDiscriminant D S C z g r σ δ) q)
    (r := r) (σ := σ) (R := R) (R₀ := R₀) (δ := δ) (ρ := ρ)
    (lV := lV) (uV := uV) (la := la) (ua := ua)
    hR hR₀ hδ hscale hscaleR hla hstrip hjets hvalues

/-- Any previously selected positive scale and band can be retained.
Only a smaller band is chosen, uniformly over all states and angles. -/
theorem n01_exists_dividedRootBand
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ r σ : ℝ, ∀ g : ℝ → ℝ, ∀ R : ℝ,
      r ∈ radialCore D → (σ = 1 ∨ σ = -1) →
      ∀ hR : 0 < R, ContDiff ℝ ∞ g →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ R) →
      ∀ δ η : ℝ, 0 < δ → 0 < η →
      ∃ ρ lV uV κ : ℝ, ∃ B : ℕ → ℝ,
        0 < ρ ∧ ρ ≤ η ∧ δ * ρ ≤ R / 4 ∧
        0 < lV ∧ lV ≤ uV ∧ 0 < κ ∧ (∀ n, 0 < B n) ∧
        N01DividedRootBandBound D S C base low outLoss ε r σ g hR δ ρ lV uV κ B := by
  obtain ⟨low, outLoss, hfactor⟩ := n01_scaledDividedFactor_fixed_loss_bound hS hT hN
  refine ⟨low, outLoss, ?_⟩
  intro r σ g R hr hσ hR hg hstrip δ η hδ hη
  obtain ⟨_, hD⟩ := hN.1.1
  have hP : RadialPartition D := hD.2.1
  obtain ⟨j, s, hs, hcellS⟩ := exists_radialCell_collar_of_partition hP hr
  let R₀ := min (R / 4) (s / 4)
  have hR₀ : 0 < R₀ := lt_min (div_pos hR (by norm_num)) (div_pos hs (by norm_num))
  have hR₀R : R₀ ≤ R / 4 := min_le_left _ _
  have hR₀s : R₀ ≤ s / 4 := min_le_right _ _
  have hphysical : Ioo ((r - R₀) - R₀) ((r + R₀) + R₀) ⊆ Ioo D.a D.b := by
    intro y hy
    apply hP.2.2.2.1 j
    apply hcellS
    constructor <;> linarith [hy.1, hy.2]
  have hcell : Ioo (r - R₀) (r + R₀) ⊆ D.cells j := by
    intro y hy
    apply hcellS
    constructor <;> linarith [hy.1, hy.2]
  have hphysicalInner : Ioo (r - R₀) (r + R₀) ⊆ Ioo D.a D.b := by
    intro y hy
    apply hphysical
    constructor <;> linarith [hy.1, hy.2]
  have hstrip₀ (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
      (hsector : stateSector S z.1) :
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R₀ := by
    intro q hq
    apply hstrip z hz hsector q
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hq.1.1, hq.1.2]
  obtain ⟨B, hB, hbound⟩ := hfactor r σ g R₀ hσ hR₀ hg hphysical j hcell hstrip₀ δ
  obtain ⟨lV, uV, la, ua, hlV, hla, hVu, hau, hvalues⟩ :=
    n01_rootCoefficient_positive_value_rectangle hS hT hN hσ hR₀ hg hphysicalInner hstrip₀
  let ρ := min η (R₀ / (2 * δ))
  have hρ : 0 < ρ := lt_min hη (div_pos hR₀ (mul_pos (by norm_num) hδ))
  have hscale : δ * ρ ≤ R₀ / 2 := by
    calc
      _ ≤ δ * (R₀ / (2 * δ)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le
      _ = _ := by field_simp [hδ.ne'] <;> ring
  have hscaleR : δ * ρ ≤ R / 4 := by linarith
  refine ⟨ρ, lV, uV, Real.sqrt lV / ua, B, hρ, min_le_left _ _, hscaleR,
    hlV, hVu, div_pos (Real.sqrt_pos.mpr hlV) (hla.trans_le hau), hB, ?_⟩
  exact n01_dividedRootBand_of_rectangle hR hR₀ hδ hscale hscaleR hla
    hstrip B hbound hvalues

end ContinuousFlexibility.Analysis
