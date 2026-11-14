module

public import ContinuousFlexibility.Analysis.N07aMaterialPieceBounds
public import ContinuousFlexibility.Analysis.N01cMixedPowerBounds

/-!
# Material weights at the actual positive inverse point

The reference ratio atoms control every point of the fixed physical
interval. Positive current pieces have that same interval, so their
actual inverse points use the original sample. The height exponent and
the distinction between zeroth and positive parameter orders are kept.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04Realization_material_weight_of_ratios
    {E Es H Hs F P γ : ℝ}
    (hE : 0 ≤ E) (hEs : 0 ≤ Es) (hH : 0 ≤ H) (hHs : 0 ≤ Hs)
    (hF : 1 ≤ F) (hP : 0 ≤ P) (hγ : 0 ≤ γ)
    (hEE : E ≤ F * Es) (hHH : H ≤ F * Hs) (k : ℕ) :
    E ^ P * parameterHeightWeight (H ^ γ) k ≤
      F ^ (P + γ) * Es ^ P * parameterHeightWeight (Hs ^ γ) k := by
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hEp := Real.rpow_le_rpow hE hEE hP
  have hHp := Real.rpow_le_rpow hH hHH hγ
  cases k with
  | zero =>
      simp only [parameterHeightWeight, ite_true, mul_one]
      calc
        E ^ P ≤ (F * Es) ^ P := hEp
        _ = F ^ P * Es ^ P := Real.mul_rpow hF0 hEs
        _ ≤ F ^ (P + γ) * Es ^ P :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hF (le_add_of_nonneg_right hγ))
            (Real.rpow_nonneg hEs P)
  | succ k =>
      simp only [parameterHeightWeight, Nat.succ_ne_zero, ite_false]
      calc
        E ^ P * H ^ γ ≤ (F * Es) ^ P * (F * Hs) ^ γ :=
          mul_le_mul hEp hHp (Real.rpow_nonneg hH γ)
            (Real.rpow_nonneg (mul_nonneg hF0 hEs) P)
        _ = F ^ (P + γ) * Es ^ P * Hs ^ γ := by
          rw [Real.mul_rpow hF0 hEs, Real.mul_rpow hF0 hHs,
            Real.rpow_add (zero_lt_one.trans_le hF) P γ]
          ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

/-- This extraction retains the explicit sampled coefficient envelope. -/
theorem n04Realization_reference_physical_material_ratios
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hinterval : ∀ m, K.physicalLeft m < K.physicalRight m) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      T.E0 p.1 / T.E0 (T.sample (K.cell m)) ≤
          B * T.E0 (T.sample (K.cell m)) ^ B ∧
        T.H p.1 / T.H (T.sample (K.cell m)) ≤
          B * T.E0 (T.sample (K.cell m)) ^ B := by
  let B : ℝ := (href.2 0).choose
  have hB : 0 < B := (href.2 0).choose_spec.1
  have hbound := (href.2 0).choose_spec.2
  refine ⟨B, hB, fun m p hp => ?_⟩
  let x : PolarPoint := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m p
  have hx : x ∈ CanonicalGeometry.unitStrip :=
    n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) (hinterval m) hp
  have hpoint : CanonicalGeometry.physicalUnitPoint K m x = p :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) (hinterval m) p
  have hb (a : CanonicalGeometry.Atom) :
      CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m a x ≤
        B * T.E0 (T.sample (K.cell m)) ^ B := by
    have h := hbound m a x hx 0 0 (by omega)
    rw [spaces_mixedDerivative_zero] at h
    exact (le_abs_self _).trans h
  have hE := hb .ratioE0
  have hH := hb .ratioH
  change T.E0 (CanonicalGeometry.physicalUnitPoint K m x).1 /
    T.E0 (T.sample (K.cell m)) ≤ _ at hE
  change T.H (CanonicalGeometry.physicalUnitPoint K m x).1 /
    T.H (T.sample (K.cell m)) ≤ _ at hH
  rw [hpoint] at hE hH
  exact ⟨hE, hH⟩

theorem n04Realization_positive_inverse_material_ratios
    {base : ℕ} {ε : ℝ} (hA : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) :
    ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m, K.positive m = true → ∀ q ∈ canonicalOpen S K m,
        T.E0 (K.inverseChart z m q).1 / T.E0 (T.sample (K.cell m)) ≤
            B * T.E0 (T.sample (K.cell m)) ^ B ∧
          T.H (K.inverseChart z m q).1 / T.H (T.sample (K.cell m)) ≤
            B * T.E0 (T.sample (K.cell m)) ^ B := by
  have h := n04Realization_reference_physical_material_ratios href
    (fun m => (hA.referenceBounds m).1)
  let B : ℝ := h.choose
  refine ⟨B, h.choose_spec.1, fun z hz hs m hm q hq => ?_⟩
  have hp := (hA.charts z hz hs m).2.1 hq
  rw [(hA.domains z hz hs m).2.2.2.2.2.1 hm] at hp
  exact h.choose_spec.2 m (K.inverseChart z m q) hp

/-- A common envelope covers every parameter order, including order zero.
Only the existing reference ratios and the positive-domain identity are used. -/
theorem n04Realization_positive_inverse_material_weight
    {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hA : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    (P γ : ℝ) (hP : 0 ≤ P) (hγ : 0 ≤ γ) :
    ∃ C₀ A₀ : ℝ, 0 < C₀ ∧ 0 ≤ A₀ ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m, K.positive m = true → ∀ q ∈ canonicalOpen S K m, ∀ k : ℕ,
        T.E0 (K.inverseChart z m q).1 ^ P *
            parameterHeightWeight (T.H (K.inverseChart z m q).1 ^ γ) k ≤
          C₀ * T.E0 (T.sample (K.cell m)) ^ A₀ *
            parameterHeightWeight (T.H (T.sample (K.cell m)) ^ γ) k := by
  have hratios := n04Realization_positive_inverse_material_ratios hA href
  let B : ℝ := hratios.choose
  have hB : 0 < B := hratios.choose_spec.1
  let C₀ : ℝ := (1 + B) ^ (P + γ)
  let A₀ : ℝ := B * (P + γ) + P
  refine ⟨C₀, A₀, Real.rpow_pos_of_pos (by linarith) _,
    add_nonneg (mul_nonneg hB.le (add_nonneg hP hγ)) hP, ?_⟩
  intro z hz hs m hm q hq k
  let Es : ℝ := T.E0 (T.sample (K.cell m))
  let Hs : ℝ := T.H (T.sample (K.cell m))
  let x : PolarPoint := K.inverseChart z m q
  have hx : x ∈ annularOpen D :=
    (hA.domains z hz hs m).2.2.1 ((hA.charts z hz hs m).2.1 hq)
  have hp := hT.2.1 x.1 hx.1
  have hsamp := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  have hEs : 0 < Es := hsamp.2.2.1
  have hHs : 0 < Hs := hsamp.2.1
  let F : ℝ := (1 + B) * Es ^ B
  have hF : 1 ≤ F := one_le_mul_of_one_le_of_one_le (by linarith)
    (Real.one_le_rpow (hfloor m) hB.le)
  have hBF : B * Es ^ B ≤ F :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hEs.le B)
  have hr := hratios.choose_spec.2 z hz hs m hm q hq
  have hEE : T.E0 x.1 ≤ F * Es :=
    (div_le_iff₀ hEs).mp (hr.1.trans hBF)
  have hHH : T.H x.1 ≤ F * Hs :=
    (div_le_iff₀ hHs).mp (hr.2.trans hBF)
  calc
    _ ≤ F ^ (P + γ) * Es ^ P * parameterHeightWeight (Hs ^ γ) k :=
      n04Realization_material_weight_of_ratios hp.2.2.1.le hEs.le hp.2.1.le hHs.le
        hF hP hγ hEE hHH k
    _ = _ := by
      dsimp only [F, C₀, A₀, Es, Hs]
      rw [Real.mul_rpow (by linarith : 0 ≤ 1 + B)
        (Real.rpow_nonneg hsamp.2.2.1.le B),
        ← Real.rpow_mul hsamp.2.2.1.le,
        Real.rpow_add hsamp.2.2.1 (B * (P + γ)) P]
      ring

end ContinuousFlexibility.Analysis
