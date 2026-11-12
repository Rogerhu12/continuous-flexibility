import ContinuousFlexibility.Analysis.N04bRootGermCollar
import ContinuousFlexibility.Analysis.N03FixedRootOrdinaryJets

/-!
# Identifying the chosen controlled root model for each actual state

The real N03 coefficient germs and angular periodicity give one collar
for a fixed state. That collar is used only to identify the same previously
chosen controlled flow and its chart near the root. Its width enters no
jet bound. No fixed correction cutoff or uniform collar over states is
assumed, and the original reference, correction and stored atlas remain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem stateRoot_storedFlow_of_coefficient_band
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R δ ρ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρw : ρ < C.right m - C.left m) (hρR : ρ ≤ R / 4)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
      let p : PolarPoint := (n01ComponentRoot C m rightEnd +
        n01ComponentRootOrientation rightEnd * t, θ)
      (L.coefficients z).a p = (originalCoefficients D S C z).a p ∧
        (L.coefficients z).b p = (originalCoefficients D S C z).b p ∧
        (L.coefficients z).c p = (originalCoefficients D S C z).c p)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z) δ) Θ) :
    RootStoredFlowAgreementOn C L z m rightEnd δ (ρ / δ) Θ := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let η := ρ / δ
  have hη : 0 < η := div_pos hρ hδ
  have hscale : δ * η = ρ := by dsimp [η]; field_simp [hδ.ne']
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  intro ι x hx
  let f : ℝ → ℝ := fun t => L.minusFlow z m (r + σ * t) ι
  have hstored := hL.2.2.2.2.1 z hz hs m ι
  have hmap : MapsTo (fun t : ℝ => r + σ * t)
      (Icc (0 : ℝ) ρ) (Icc (C.left m) (C.right m)) := by
    intro t ht
    have htwidth : t < C.right m - C.left m := ht.2.trans_lt hρw
    cases rightEnd <;>
      simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
        Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul] <;>
      constructor <;> linarith only [ht.1, htwidth]
  have hcont : ContinuousOn f (Icc (0 : ℝ) ρ) :=
    hstored.2.1.comp (continuous_const.add
      (continuous_const.mul continuous_id)).continuousOn hmap
  have hode : ∀ t ∈ Ioo (0 : ℝ) ρ,
      HasDerivAt f (rootPhysicalSpeed (localizedRootDrift D S C r σ hR z)
        (localizedRootSpeed D S C g r σ hR z) (-σ) (t, f t)) t := by
    intro t ht
    have htwidth : t < C.right m - C.left m := ht.2.trans hρw
    have hp : r + σ * t ∈ Ioo (C.left m) (C.right m) := by
      cases rightEnd <;>
        simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
          Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul] <;>
        constructor <;> linarith only [ht.1, htwidth]
    have hv :
        (L.coefficients z).a (r + σ * t, f t) =
            (originalCoefficients D S C z).a (r + σ * t, f t) ∧
          (L.coefficients z).b (r + σ * t, f t) =
            (originalCoefficients D S C z).b (r + σ * t, f t) ∧
          (L.coefficients z).c (r + σ * t, f t) =
            (originalCoefficients D S C z).c (r + σ * t, f t) :=
      hcoeff t (Ioo_subset_Icc_self ht) (f t)
    have heq : minusCharacteristicSpeed (L.coefficients z) (r + σ * t, f t) =
        minusCharacteristicSpeed (originalCoefficients D S C z) (r + σ * t, f t) := by
      simp only [minusCharacteristicSpeed, hv.1, hv.2.1, hv.2.2]
    have hraw := rootPhysicalSpeed_localization_eq_oriented_polarMinus
      (contDiff_stateProfile_of_n01 hS hT hN z.1)
      (contDiff_stateHeight_of_n01 hS hT hN z) hR hstrip
      (p := (t, f t)) ⟨ht.1.le, ht.2.le.trans hρR⟩
    have hraw' : rootPhysicalSpeed (localizedRootDrift D S C r σ hR z)
        (localizedRootSpeed D S C g r σ hR z) (-σ) (t, f t) =
        σ * minusCharacteristicSpeed (originalCoefficients D S C z) (r + σ * t, f t) :=
      hraw
    have hlin : HasDerivAt (fun s : ℝ => r + σ * s) σ t := by
      simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul σ).const_add r
    have hd := (hstored.2.2.1 (r + σ * t) hp).comp t hlin
    have hf : (fun u => L.minusFlow z m u ι) ∘ (fun s : ℝ => r + σ * s) = f := by
      funext s
      exact Function.comp_apply
    rw [hf] at hd
    change HasDerivAt f
      (minusCharacteristicSpeed (L.coefficients z) (r + σ * t, f t) * σ) t at hd
    apply hd.congr_deriv
    rw [hraw', heq]
    ring
  have hinit : f 0 = L.minusFlow z m r ι := by simp only [f, mul_zero, add_zero]
  exact rootRescaledFlow_eq_storedTrajectory (f := f) hη hδ Real.pi_ne_zero
    hregular.1 hregular.2 hperiod.1 hperiod.2 hΘ hinit
    (by simpa only [hscale] using hcont)
    (fun t ht => hode t (by simpa only [hscale] using ht)) hx

private theorem stateRoot_chart_of_glued_values
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {G : ℝ × ℝ × ℝ → ℝ} {p q : PolarPoint} (hq : 0 < q.1)
    (hp : p ∈ physicalPieceOpen S K z
      (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1))
    (ht : canonicalGluedRootTravel S K z m rightEnd p =
      q.1 ^ (3 / 2 : ℝ) * rootOddCoefficient G q)
    (ha : (canonicalGluedAiryIntegral S K z m 1 p +
      canonicalGluedAiryIntegral S K z m (-1) p) / 2 = rootEven G q) :
    K.chart z (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1) p =
      extendedRootEvenOddChart G q := by
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  have hvalues := canonicalCutPair_chartValues_of_gluedIntegrals
    m rightEnd (hB.1.2 z hz hs m).2.2.1 hp
  have htravel : airyTravelPrimitive (K.chart z i p).1 =
      q.1 ^ (3 / 2 : ℝ) * rootOddCoefficient G q := hvalues.2.trans ht
  have hangle : (K.chart z i p).2 = rootEven G q := hvalues.1.trans ha
  obtain ⟨_, _, _, _, _, _, hl, hr, _, _⟩ := hB.1.1 m
  have hzero : K.left i = 0 := by cases rightEnd <;> assumption
  have hcanonical := (hA.charts z hz hs i).1 hp
  have hnonneg : 0 ≤ (K.chart z i p).1 := by
    have hb : K.left i < (K.chart z i p).1 := hcanonical.1.1
    exact (hzero ▸ hb).le
  apply (extendedRootEvenOddChart_eq_of_travel_values hq hnonneg ?_).symm
  exact (characteristicTravelChart_rootCharacteristicCoordinate G hq).trans
    (Prod.ext htravel.symm hangle.symm)

/-- The actual stored chart agrees with the supplied controlled model on
some state-dependent band. The original scale and flow remain unchanged.
This is an identification result, not a quantitative lower bound for the
state-dependent identification radius. -/
theorem n03_exists_state_controlledRoot_band
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R δ M : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations
      (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z) δ) Θ)
    (hG : ContDiff ℝ ∞
      (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)))
    (hperiod : ∀ x ζ θ,
      rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
          (x, ζ, θ + Real.pi) =
        rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
          (x, ζ, θ) + Real.pi)
    (hCS : CSBound 1
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)
      (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)) M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ δ * ρ ≤ R / 4 ∧
      ControlledRootBandChartAgreement C K z m rightEnd δ ρ Θ ∧
      ∀ x ∈ Ioc (0 : ℝ) ρ, ∀ θ : ℝ,
        let p : PolarPoint := (n01ComponentRoot C m rightEnd +
          n01ComponentRootOrientation rightEnd * (δ * x), θ)
        (L.coefficients z).a p = (originalCoefficients D S C z).a p ∧
          (L.coefficients z).b p = (originalCoefficients D S C z).b p ∧
          (L.coefficients z).c p = (originalCoefficients D S C z).c p := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
  have hroot := n01_component_root_data hN.1.1 m rightEnd
  have hw : 0 < C.right m - C.left m := sub_pos.mpr (hN.1.1.2.2.2.1.1 m).2.1
  obtain ⟨ε₀, hε₀, hcoeffRoot⟩ :=
    n04b_through03_root_coefficient_collar hS hN hfield hz hs hroot.1 hroot.2.1
  let a := min (δ / 2) (min ((C.right m - C.left m) / 2) (min (R / 4) (ε₀ / 2)))
  have ha : 0 < a := lt_min (half_pos hδ)
    (lt_min (half_pos hw) (lt_min (div_pos hR (by norm_num)) (half_pos hε₀)))
  have haδ : a < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have haw : a < C.right m - C.left m :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hw)
  have haR : a ≤ R / 4 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have haε : a < ε₀ :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans_lt
      (half_lt_self hε₀)
  have hcoeff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) a) (θ : ℝ) :
      (L.coefficients z).a (r + σ * t, θ) = (originalCoefficients D S C z).a (r + σ * t, θ) ∧
        (L.coefficients z).b (r + σ * t, θ) = (originalCoefficients D S C z).b (r + σ * t, θ) ∧
        (L.coefficients z).c (r + σ * t, θ) = (originalCoefficients D S C z).c (r + σ * t, θ) := by
    have habs : |r + σ * t - r| = t := by
      rcases n01ComponentRootOrientation_eq rightEnd with h | h
      · rw [show σ = 1 from h]
        simpa only [one_mul, add_sub_cancel_left] using abs_of_nonneg ht.1
      · rw [show σ = -1 from h]
        simpa only [neg_one_mul, add_sub_cancel_left, abs_neg] using abs_of_nonneg ht.1
    exact (hcoeffRoot (r + σ * t) θ (by
      change |r + σ * t - r| < ε₀
      rw [habs]
      exact ht.2.trans_lt haε)).2
  let η := a / δ
  have hη : 0 < η := div_pos ha hδ
  have hηone : η ≤ 1 := (div_le_iff₀ hδ).mpr (by simpa only [one_mul] using haδ.le)
  have hscale : δ * η = a := by dsimp only [η]; field_simp [hδ.ne']
  have hmatch : RootStoredFlowAgreementOn C L z m rightEnd δ η Θ :=
    stateRoot_storedFlow_of_coefficient_band hS hT hN.1.1 hN.2 hz hs m rightEnd
      hg hR hδ ha haw haR hstrip hcoeff hΘ
  have hcut : 0 < K.cutRadius m := (hB.1.1 m).2.2.2.2.2.1
  have hcutTravel : 0 < airyTravelPrimitive (K.cutRadius m) :=
    mul_pos (by norm_num : (0 : ℝ) < 2 / 3) (Real.rpow_pos_of_pos hcut _)
  obtain ⟨ρ, hρ, hρη, hsmall⟩ :=
    exists_rootTravel_uniform_small_band hη hηone hcutTravel hM
  have hρR : δ * ρ ≤ R / 4 := by
    calc
      δ * ρ ≤ δ * η := mul_le_mul_of_nonneg_left hρη hδ.le
      _ = a := hscale
      _ ≤ R / 4 := haR
  refine ⟨ρ, hρ, hρη.trans hηone, hρR, ?_, ?_⟩
  · dsimp only [ControlledRootBandChartAgreement]
    intro x hx θ
    have hdx : 0 < δ * x := mul_pos hδ hx.1
    have hdxwidth : δ * x < C.right m - C.left m := by
      calc
        δ * x ≤ δ * η := mul_le_mul_of_nonneg_left (hx.2.trans hρη) hδ.le
        _ = a := hscale
        _ < C.right m - C.left m := haw
    have hphysical : r + σ * (δ * x) ∈ Ioo (C.left m) (C.right m) := by
      cases rightEnd <;>
        simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
          Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul, Set.mem_Ioo] <;>
        constructor <;> linarith only [hdx, hdxwidth]
    have hvalues := n03_rootTravel_eq_controlledRootTravel_on_band
      hS hT hN.1.1 hN.1.2 hN.2 hA hB hz hs m rightEnd hg hR hstrip hΘ
      hmatch ⟨hx.1, hx.2.trans hρη⟩ hphysical θ
    have htravel := hsmall G hG hperiod hCS x ⟨hx.1.le, hx.2⟩ θ
    have hown := canonicalCutPair_mem_own_half_of_rootTravel_lt hA hB hz hs m rightEnd
      ⟨hphysical, mem_univ θ⟩ (hvalues.1.trans_lt htravel)
    exact ⟨hown, stateRoot_chart_of_glued_values hA hB hz hs m rightEnd
      hx.1 hown hvalues.1 hvalues.2⟩
  · intro x hx θ
    have ht : δ * x ∈ Icc (0 : ℝ) a := by
      refine ⟨(mul_pos hδ hx.1).le, ?_⟩
      calc
        δ * x ≤ δ * η := mul_le_mul_of_nonneg_left (hx.2.trans hρη) hδ.le
        _ = a := hscale
    exact hcoeff (δ * x) ht θ

end ContinuousFlexibility.Analysis
