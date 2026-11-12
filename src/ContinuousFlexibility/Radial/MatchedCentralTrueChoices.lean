import ContinuousFlexibility.Radial.FixedCentralModelSmallError
import ContinuousFlexibility.Radial.MatchedCentralTrueEnvelope
import ContinuousFlexibility.Radial.FixedCentralBorder
import ContinuousFlexibility.Radial.CentralModelSlopeWindow
import ContinuousFlexibility.Radial.InnerBufferLocalizedConstruction

/-!
# A true central model chosen before the retained tails

The physical border is fixed first. Its full-model bound, truncation
radius and actual localized witnesses are then chosen uniformly over
all even frequencies. No later reference, retained length or number of
Morse pieces occurs in these choices.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

theorem matchedFixedCentralColumn_positive_support (B : FixedCentralBorder) :
    tsupport (fixedCentralColumn B.chi) ⊆ Ioi 0 := by
  intro r hr
  exact fixedCentralCap_order.1.trans (B.column_support hr).1

theorem matchedFixedCentralColumn_support_at_cut (B : FixedCentralBorder)
    {T : ℝ} (hT : 0 ≤ T) (hcap : sqrt centralOscillatorA + 2 ≤ T) :
    Function.support (fixedCentralColumn B.chi) ⊆
      Ioo (centralRadius (-T)) (centralRadius T) := by
  intro r hr
  have hs := B.column_support (subset_tsupport (fixedCentralColumn B.chi) hr)
  constructor
  · apply lt_of_le_of_lt (b := fixedCentralCapLeft) _ hs.1
    exact strictMono_centralRadius.monotone (by linarith [sqrt_nonneg centralOscillatorA])
  · exact hs.2.trans_le (strictMono_centralRadius.monotone hcap)

/-- The true border is fixed before every tolerance, model radius and
retained geometry. The one localized witness carries all its actual
Poisson remainder and conormal estimates. -/
theorem exists_matchedCentralTrueModelChoices
    (hR09 : R09Statement) (B : FixedCentralBorder) :
    ∃ C K B₀ : ℝ, 0 < C ∧ 0 < K ∧ 0 < B₀ ∧
      ∀ η : ℝ, 0 < η → ∀ initial : ℝ, ∃ T : ℝ,
        initial ≤ T ∧ 8 ≤ T ∧
        Function.support (fixedCentralColumn B.chi) ⊆
          Ioo (centralRadius (-T)) (centralRadius T) ∧
        (∀ r : ℝ, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
          (3 / 4 : ℝ) ≤
            r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r) ∧
        (∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ centralBufferMass j T) ∧
        ∀ q : ℕ, 1 ≤ q →
          let b := centralModelBuffer (2 * (q : ℝ)) T B₀ (centralModelBordered q)
            (centralModelPhysicalColumn (by norm_num : (0 : ℝ) < 1)
              B.column_smooth B.column_compact (matchedFixedCentralColumn_positive_support B))
            (centralModelPhysicalColumnFunction 1 (fixedCentralColumn B.chi))
          BufferHypotheses b ∧ ∃ M : InnerBufferLocalizedData b C K,
            (∀ i, 0 < (M.column i).inwardEnergy + bufferSign i * centralRadiusA ∧
              (M.column i).inwardEnergy ≤
                2 * ((M.column i).inwardEnergy + bufferSign i * centralRadiusA)) ∧
            (∀ i, (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
              (innerBufferRemainderEnvelope b C K i /
                sqrt ((M.column i).inwardEnergy + bufferSign i * centralRadiusA)) <
                  min 1 η / (2 * (q : ℝ))) ∧
            ∀ height : ℝ, 0 < height → ∀ sign : Bool,
              ‖innerTwoCutWeightedError
                (innerPhysicalCutKappa height
                  (fun i => centralDensityRoot (bufferCut b i))
                  (fun i => (M.column i).inwardEnergy + bufferSign i * centralRadiusA))
                (fun _ => 1)
                (M.physicalFluxError height (fun i => centralDensityRoot (bufferCut b i))) sign‖ <
                η := by
  let g := centralModelPhysicalColumn (by norm_num : (0 : ℝ) < 1)
    B.column_smooth B.column_compact (matchedFixedCentralColumn_positive_support B)
  let f := centralModelPhysicalColumnFunction 1 (fixedCentralColumn B.chi)
  have hgpair : ⟪centralModelGroundVector, g⟫_ℝ ≠ 0 := by
    apply centralModelPhysicalColumn_ground_pairing_ne_zero
      (by norm_num : (0 : ℝ) < 1) B.column_smooth B.column_compact
      (matchedFixedCentralColumn_positive_support B)
    rw [B.column_pairing]
    exact one_ne_zero
  obtain ⟨B₀, hB₀, hfull⟩ := exists_central_even_full_inverse_bound g hgpair
  obtain ⟨C, ε, hC, hε, hcompress⟩ := hR09 64 (by norm_num)
  obtain ⟨K, hK, hlocalized⟩ := exists_innerBufferLocalizedData
  obtain ⟨Tmin, _, hcap, hwindow⟩ := exists_centralModel_logSlope_window
  refine ⟨C, K, B₀, hC, hK, hB₀, ?_⟩
  intro η hη initial
  let A := matchedCentralTrueAmplitude B₀ C K
  have hfactor := matchedCentralTrueAmplitude_bounds (B₀ := B₀) hC.le hK.le
  have hApos : 0 < A := zero_lt_one.trans_le
    ((innerCentralCompressionAmplitude_ge_one (C + B₀)).trans hfactor.1)
  obtain ⟨L₀, hL₀, hsuppress⟩ := inner_product_frequency_suppression
    (A := log A) (b := 2) (d := 8) (c := 1 / 16) (η := min 1 η)
    (by norm_num) (by norm_num) (by norm_num) (lt_min zero_lt_one hη)
  obtain ⟨T, hT, hfloor, hsupp, hsmall⟩ := exists_centralBuffer_radius
    (centralModelPhysicalColumnFunction_hasCompactSupport 1 B.column_compact
      (matchedFixedCentralColumn_positive_support B)) hB₀.le hε
      (max initial (max Tmin (max L₀ (4 * C * centralRadiusA))))
  have hrest : max Tmin (max L₀ (4 * C * centralRadiusA)) ≤ T :=
    (le_max_right _ _).trans hfloor
  have hmin : Tmin ≤ T := (le_max_left _ _).trans hrest
  have hrest' : max L₀ (4 * C * centralRadiusA) ≤ T :=
    (le_max_right _ _).trans hrest
  have hLT : L₀ ≤ T := (le_max_left _ _).trans hrest'
  have hfarT : 4 * C * centralRadiusA ≤ T := (le_max_right _ _).trans hrest'
  have hfar (j : ℝ) (hj : 2 ≤ j) :
      2 * C * centralRadiusA ≤ centralBufferMass j T := by
    have hp := mul_le_mul_of_nonneg_right hj (show (0 : ℝ) ≤ T by linarith only [hT])
    unfold centralBufferMass
    nlinarith only [hp, hfarT]
  have hT1 : (1 : ℝ) ≤ T := hL₀.trans hLT
  have hLs : L₀ ≤ T ^ 2 := hLT.trans
    (by nlinarith only [hT1, sq_nonneg (T - 1)] : T ≤ T ^ 2)
  refine ⟨T, (le_max_left _ _).trans hfloor, hT,
    matchedFixedCentralColumn_support_at_cut B (by linarith only [hT]) (hcap.trans hmin),
    hwindow T hmin, hfar, ?_⟩
  intro q hq
  have hj := innerCentralBuffer_frequency hq
  have hjpos : (0 : ℝ) < 2 * (q : ℝ) := (by norm_num : (0 : ℝ) < 2).trans_le hj
  let b := centralModelBuffer (2 * (q : ℝ)) T B₀ (centralModelBordered q) g f
  obtain ⟨H, hHnorm, hHsolve, hHunique⟩ := hfull q hq
  have hb : BufferHypotheses b := centralModelBuffer_hypotheses
    (centralModelBordered q) g f hj hT hB₀
    (contDiff_centralModelPhysicalColumnFunction (by norm_num : (0 : ℝ) < 1) B.column_smooth)
    (centralModelPhysicalColumnFunction_hasCompactSupport 1 B.column_compact
      (matchedFixedCentralColumn_positive_support B))
    (centralModelPhysicalColumn_ae (by norm_num : (0 : ℝ) < 1)
      B.column_smooth B.column_compact (matchedFixedCentralColumn_positive_support B))
    hsupp H hHnorm hHsolve hHunique
  have hcompression : BufferCompressionConclusion b C :=
    hcompress b (show b.layerBound ≤ 64 from le_rfl) hb
      (fun _ => hsmall (2 * (q : ℝ)) hj)
  obtain ⟨M⟩ := hlocalized b C hb hcompression
  have heq := innerCentralCompressionEnvelope_eq_exp (X₀ := T) hApos hjpos.le
  have henv : innerCentralCompressionEnvelope A T (2 * (q : ℝ)) < min 1 η ∧
      (2 * (q : ℝ)) * innerCentralCompressionEnvelope A T (2 * (q : ℝ)) < min 1 η := by
    simpa only [heq] using hsuppress (T ^ 2) hLs (2 * (q : ℝ))
      ((by norm_num : (1 : ℝ) ≤ 2).trans hj)
  have hmass := hfar (2 * (q : ℝ)) hj
  refine ⟨hb, M, (fun i => fixedCentralModelCutEnergy_bounds (B := B) M hC hmass i), ?_, ?_⟩
  · intro i
    apply (lt_div_iff₀ hjpos).mpr
    have hr := matchedCentralTrueRemainder_le_envelope hb M hq hT hC hK.le
      hmass hfactor.2.1 i
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hr hjpos.le).trans_lt henv.2
  · intro height hh sign
    exact (matchedCentralTrueFluxError_le_envelope hb M hq hT hC hmass
      hfactor.2.2 hh sign).trans_lt (henv.1.trans_le (min_le_right 1 η))

/-- The earlier weak choice interface is a thin consequence of the
same fully quantitative construction. -/
theorem exists_matchedCentralTrueLocalizedChoices
    (hR09 : R09Statement) (B : FixedCentralBorder) (initial : ℝ) :
    ∃ C K B₀ T : ℝ, 0 < C ∧ 0 < K ∧ 0 < B₀ ∧ 8 ≤ T ∧ initial ≤ T ∧
      Function.support (fixedCentralColumn B.chi) ⊆
        Ioo (centralRadius (-T)) (centralRadius T) ∧
      (∀ r : ℝ, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
        (3 / 4 : ℝ) ≤
          r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r) ∧
      ∀ q : ℕ, 1 ≤ q →
        let b := centralModelBuffer (2 * (q : ℝ)) T B₀ (centralModelBordered q)
          (centralModelPhysicalColumn (by norm_num : (0 : ℝ) < 1)
            B.column_smooth B.column_compact (matchedFixedCentralColumn_positive_support B))
          (centralModelPhysicalColumnFunction 1 (fixedCentralColumn B.chi))
        BufferHypotheses b ∧ Nonempty (InnerBufferLocalizedData b C K) := by
  obtain ⟨C, K, B₀, hC, hK, hB₀, hchoice⟩ := exists_matchedCentralTrueModelChoices hR09 B
  obtain ⟨T, hinit, hT, hsupp, hwindow, _, hmodels⟩ := hchoice 1 (by norm_num) initial
  refine ⟨C, K, B₀, T, hC, hK, hB₀, hT, hinit, hsupp, hwindow, ?_⟩
  intro q hq
  obtain ⟨hb, M, _⟩ := hmodels q hq
  exact ⟨hb, ⟨M⟩⟩

end ContinuousFlexibility.Radial
