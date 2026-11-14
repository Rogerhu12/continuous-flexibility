module

public import ContinuousFlexibility.Analysis.N04RealizationSampleWeight
public import ContinuousFlexibility.Analysis.N07aAngularReferenceJetEnvelopes
public import ContinuousFlexibility.Analysis.CanonicalActualWholeGeometry

/-!
# Quantitative bounds for the same global reference transport

The current inverse chart is estimated on its genuine canonical domain.
Composing with the reference chart controls the actual reference-to-current
map. The reciprocal current height is evaluated at that same inverse point;
its existing source-factor and inverse-Jacobian estimate therefore gives the
actual transported height ratio. These fixed-state envelopes use only the
reference and current coordinate jets, not primitive material jets.

One power of the physical material weight absorbs every finite sampled
envelope. Global C3 regularity extends the estimates through order two across
the radial interfaces. The final theorem attaches all four quantitative
bounds to the already constructed qualitative transport on one neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

/-- Positive-order composition does not require a zeroth-order bound for
either map. In particular it applies to unwrapped angular coordinates. -/
theorem n04Realization_positive_jets_comp
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set E} {V : ℕ → Set F}
    {f : ℕ → F → G} {Φ : ℕ → E → F}
    (hmaps : ∀ m, MapsTo (Φ m) (W m) (V m))
    (hfs : ∀ m x, x ∈ W m → ContDiffAt ℝ ∞ (f m) (Φ m x))
    (hΦs : ∀ m x, x ∈ W m → ContDiffAt ℝ ∞ (Φ m) x)
    (hf : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m y, y ∈ V m → ‖iteratedFDeriv ℝ n (f m) y‖ ≤ e m)
    (hΦ : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m x, x ∈ W m → ‖iteratedFDeriv ℝ n (Φ m) x‖ ≤ e m) :
    ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m x, x ∈ W m → ‖iteratedFDeriv ℝ n (f m ∘ Φ m) x‖ ≤ e m := by
  classical
  intro n hn
  choose a ha ha0 hab using fun c : OrderedFinpartition n => hf c.length (c.length_pos hn)
  choose b hb hb0 hbb using fun c : OrderedFinpartition n =>
    fun j : Fin c.length => hΦ (c.partSize j) (c.partSize_pos j)
  let e : OrderedFinpartition n → ℕ → ℝ := fun c m => a c m * ∏ j, b c j m
  have he (c : OrderedFinpartition n) : N07aSampleSubpower T K (e c) :=
    N07aSampleSubpower.mul hD hT (ha c)
      (N07aSampleSubpower.finset_prod hD hT Finset.univ (b c) (fun j _ => hb c j))
  refine ⟨fun m => ∑ c, e c m,
    N07aSampleSubpower.finset_sum hD hT Finset.univ e (fun c _ => he c),
    fun m => Finset.sum_nonneg (fun c _ =>
      mul_nonneg (ha0 c m) (Finset.prod_nonneg (fun j _ => hb0 c j m))), ?_⟩
  intro m x hx
  apply (norm_iteratedFDeriv_comp_le_partition_sum (hfs m x hx) (hΦs m x hx) n).trans
  apply Finset.sum_le_sum
  intro c _
  have hprod : (∏ j, ‖iteratedFDeriv ℝ (c.partSize j) (Φ m) x‖) ≤ ∏ j, b c j m :=
    Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hbb c j m x hx)
  exact mul_le_mul (hab c m (Φ m x) (hmaps m hx)) hprod
    (Finset.prod_nonneg (fun j _ => norm_nonneg _)) (ha0 c m)

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {base loss : ℕ} {ε : ℝ}

/-- The actual transition and actual height quotient have fixed-state
sampled jet envelopes on every reference physical piece. -/
theorem n04Realization_reference_transport_piece_jets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) :
    (∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
          ‖iteratedFDeriv ℝ n (canonicalCurrentPoint C K (liftSectorParameter S C z) m) p‖ ≤ e m) ∧
    N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K) (fun _ => 1)
      (fun m p => K.height (C.referenceState, 0) m p /
        K.height (liftSectorParameter S C z) m
          (canonicalCurrentPoint C K (liftSectorParameter S C z) m p)) := by
  let z' : AnnularState S × ℝ := liftSectorParameter S C z
  let R : ℕ → Set PolarPoint := referencePhysicalPieceOpen S K
  let V : ℕ → Set PolarPoint := canonicalOpen S K
  let Ψ : ℕ → PolarPoint → PolarPoint := K.inverseChart z'
  let Φ : ℕ → PolarPoint → PolarPoint := K.chart (C.referenceState, 0)
  have hR : ∀ m, IsOpen (R m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hV : ∀ m, IsOpen (V m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := hrefState.liftSectorParameter_sector z
  have hc (m : ℕ) := h04.1.charts z' hz' hs m
  have hr (m : ℕ) := h04.1.charts (C.referenceState, 0)
    (reference_mem_stateNeighborhood S C base hε) hrefState.stateSector m
  simp only [h04.1.referenceDomain] at hr
  have hphysical := fun m => (h04.1.referenceBounds m).1
  have hinterval := fun m => (h04.1.referenceBounds m).2.1
  have hΦb := n07a_physicalChart_positive_fixedEnvelope hD hT href hinterval hphysical
    (fun m a => (href.1 m a).1)
    (n07a_referencePhysicalJetFields_fixedEnvelope hD hT href hphysical)
  have hΨb := n07a_currentInverseChart_positive_fixedEnvelope hD hT h04 href hcur z hz
  have htransition := n04Realization_positive_jets_comp hD hT
    (fun m => (hr m).1)
    (fun m p hp => (hc m).2.2.2.2.2.1.contDiffAt ((hV m).mem_nhds ((hr m).1 hp)))
    (fun m p hp => (hr m).2.2.2.2.1.contDiffAt ((hR m).mem_nhds hp)) hΨb hΦb
  have hInv : N07aAngularFixedJetEnvelope T K V (fun _ => 1)
      (fun m y => (K.height z' m (Ψ m y))⁻¹) :=
    n07a_currentCanonicalHeightInverse_fixedJetEnvelope hD hT hrefState h04 href hcur z hz
  have hInvsm (m : ℕ) : ContDiffOn ℝ ∞
      (fun y => (K.height z' m (Ψ m y))⁻¹) (V m) :=
    ((hc m).2.2.2.2.2.2.1.comp (hc m).2.2.2.2.2.1 (hc m).2.1).inv
      (fun y hy => ((hc m).2.2.2.2.2.2.2 _ ((hc m).2.1 hy)).1.ne')
  have hback : N07aAngularFixedJetEnvelope T K R (fun _ => 1)
      (fun m => (fun y => (K.height z' m (Ψ m y))⁻¹) ∘ Φ m) :=
    hInv.comp hD hT (fun _ => zero_le_one) (fun m => (hr m).1)
      (fun m p hp => (hInvsm m).contDiffAt ((hV m).mem_nhds ((hr m).1 hp)))
      (fun m p hp => (hr m).2.2.2.2.1.contDiffAt ((hR m).mem_nhds hp)) hΦb
  have hbacksm (m : ℕ) : ContDiffOn ℝ ∞
      ((fun y => (K.height z' m (Ψ m y))⁻¹) ∘ Φ m) (R m) :=
    (hInvsm m).comp (hr m).2.2.2.2.1 (hr m).1
  have hheight : N07aAngularFixedJetEnvelope T K R (fun _ => 1)
      (fun m => K.height (C.referenceState, 0) m) := by
    simpa only [n07aPhysicalJetField, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
      n07a_referencePhysicalJetFields_fixedEnvelope hD hT href hphysical 2
  have hprod : N07aAngularFixedJetEnvelope T K R (fun _ => 1)
      (fun m p => K.height (C.referenceState, 0) m p *
        (((fun y => (K.height z' m (Ψ m y))⁻¹) ∘ Φ m) p)) := by
    simpa only [one_mul] using N07aAngularFixedJetEnvelope.mul hD hT hR
      (fun m => (hr m).2.2.2.2.2.2.1) hbacksm hheight hback
      (fun _ => zero_le_one) (fun _ => zero_le_one)
  refine ⟨htransition, hprod.congr hR ?_⟩
  intro m p _
  simp only [canonicalCurrentPoint, Function.comp_apply, div_eq_mul_inv, Ψ, Φ, z']

/-- The prescribed global functions inherit the actual first two transport
jets. Their constants may depend on the state, as in the frozen certificate. -/
theorem n04Realization_transport_C2_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {τ : PolarPoint → PolarPoint} {q : PolarPoint → ℝ}
    (hτ : ContDiffOn ℝ 3 τ (annularOpen D)) (hq : ContDiffOn ℝ 3 q (annularOpen D))
    (hagree : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      τ p = canonicalCurrentPoint C K z m p ∧
        q p = K.height (C.referenceState, 0) m p / K.height z m (τ p)) :
    ∃ B : ℝ, 0 < B ∧
      (∀ p ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
        ‖iteratedFDeriv ℝ n q p‖ ≤ B * T.M p.1) ∧
      (∀ p ∈ annularOpen D, ∀ n : ℕ, 1 ≤ n → n ≤ 2 →
        ‖iteratedFDeriv ℝ n τ p‖ ≤ B * T.M p.1) := by
  let ζ : StateDirections S × ℝ :=
    (⟨z.1 - C.referenceState,
      (stateSectorSubmodule S).sub_mem hs hrefState.stateSector⟩, z.2)
  have hζ : ζ ∈ sectorNeighborhood S base ε ε := hz
  have hζz : liftSectorParameter S C ζ = z := by
    apply Prod.ext
    · change C.referenceState + (z.1 - C.referenceState) = z.1
      exact (add_comm _ _).trans (sub_add_cancel _ _)
    · rfl
  have hjets := n04Realization_reference_transport_piece_jets hD hT hε hrefState h04 href hcur ζ hζ
  rw [hζz] at hjets
  have hqeq (m : ℕ) : EqOn q
      (fun p => K.height (C.referenceState, 0) m p / K.height z m (canonicalCurrentPoint C K z m p))
      (referencePhysicalPieceOpen S K m) := by
    intro p hp
    rw [(hagree m p hp).2, (hagree m p hp).1]
  have hqbound (n : ℕ) (hn : n ≤ 2) : ∃ B : ℝ, 0 < B ∧
      ∀ p ∈ annularOpen D, ‖iteratedFDeriv ℝ n q p‖ ≤ B * T.M p.1 := by
    obtain ⟨e, he, _, heb⟩ := hjets.2 n
    exact n04Realization_iteratedFDeriv_weighted_bound hD hT h04.1 href hq hqeq hn he
      (fun m p hp => by simpa only [mul_one] using heb m p hp)
  have hτbound (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 2) : ∃ B : ℝ, 0 < B ∧
      ∀ p ∈ annularOpen D, ‖iteratedFDeriv ℝ n τ p‖ ≤ B * T.M p.1 := by
    obtain ⟨e, he, _, heb⟩ := hjets.1 n hn0
    exact n04Realization_iteratedFDeriv_weighted_bound hD hT h04.1 href hτ
      (fun m p hp => (hagree m p hp).1) hn he heb
  obtain ⟨Q₀, hQ₀, hbQ₀⟩ := hqbound 0 (by omega)
  obtain ⟨Q₁, hQ₁, hbQ₁⟩ := hqbound 1 (by omega)
  obtain ⟨Q₂, hQ₂, hbQ₂⟩ := hqbound 2 (by omega)
  obtain ⟨F₁, hF₁, hbF₁⟩ := hτbound 1 (by omega) (by omega)
  obtain ⟨F₂, hF₂, hbF₂⟩ := hτbound 2 (by omega) (by omega)
  let B : ℝ := Q₀ + Q₁ + Q₂ + F₁ + F₂
  have hB : 0 < B := by dsimp only [B]; positivity
  have hQ₀B : Q₀ ≤ B := by dsimp only [B]; linarith
  have hQ₁B : Q₁ ≤ B := by dsimp only [B]; linarith
  have hQ₂B : Q₂ ≤ B := by dsimp only [B]; linarith
  have hF₁B : F₁ ≤ B := by dsimp only [B]; linarith
  have hF₂B : F₂ ≤ B := by dsimp only [B]; linarith
  have hM (p : PolarPoint) (hp : p ∈ annularOpen D) : 0 ≤ T.M p.1 :=
    zero_le_one.trans (hT.2.1 _ hp.1).2.2.2
  refine ⟨B, hB, ?_, ?_⟩
  · intro p hp n hn
    interval_cases n
    · exact (hbQ₀ p hp).trans (mul_le_mul_of_nonneg_right hQ₀B (hM p hp))
    · exact (hbQ₁ p hp).trans (mul_le_mul_of_nonneg_right hQ₁B (hM p hp))
    · exact (hbQ₂ p hp).trans (mul_le_mul_of_nonneg_right hQ₂B (hM p hp))
  · intro p hp n hn0 hn
    interval_cases n
    · exact (hbF₁ p hp).trans (mul_le_mul_of_nonneg_right hF₁B (hM p hp))
    · exact (hbF₂ p hp).trans (mul_le_mul_of_nonneg_right hF₂B (hM p hp))

/-- The exact primitive transport clause follows from the actual reference
and current jets and the already constructed global qualitative maps. The
single exponent is one; the normalized `E0` floor pays for the bounded ratios. -/
theorem n04Realization_transport_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hE0 : ∀ r ∈ radialCore D, 1 ≤ T.E0 r)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hqual : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ τ : PolarPoint → PolarPoint, ∃ q : PolarPoint → ℝ,
        WholeCanonicalTransportQualitative (D := D) C K z τ q) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
        ∃ τ : PolarPoint → PolarPoint, ∃ q : PolarPoint → ℝ,
          ContDiffOn ℝ 3 τ (annularOpen D) ∧ ContDiffOn ℝ 3 q (annularOpen D) ∧
          MapsTo τ (annularOpen D) (annularOpen D) ∧
          (∀ p, τ (p + (0, Real.pi)) = τ p + (0, Real.pi)) ∧
          Function.Periodic q (0, Real.pi) ∧
          (∀ p, τ (p.1, -p.2) = ((τ p).1, -(τ p).2)) ∧
          (∀ r θ, q (r, -θ) = q (r, θ)) ∧
          (∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
            τ p = canonicalCurrentPoint C K z m p ∧
              q p = K.height (C.referenceState, 0) m p / K.height z m (τ p)) ∧
          ∃ C₀ A : ℝ, 0 < C₀ ∧ 0 ≤ A ∧
            (∀ p ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
              ‖iteratedFDeriv ℝ n q p‖ ≤ C₀ * T.M p.1 ^ A) ∧
            (∀ p ∈ annularOpen D, ∀ n : ℕ, 1 ≤ n → n ≤ 2 →
              ‖iteratedFDeriv ℝ n τ p‖ ≤ C₀ * T.M p.1 ^ A) ∧
            (∀ p ∈ annularOpen D,
              T.H (τ p).1 / T.H p.1 ≤ C₀ * T.E0 p.1 ^ A) ∧
            (∀ p ∈ annularOpen D,
              T.M (τ p).1 / T.M p.1 ≤ C₀ * T.E0 p.1 ^ A) := by
  obtain ⟨base', hb, η, hη, hηε, hratios⟩ :=
    n04Realization_transport_weight_ratios_neighborhood hD hT hε hrefState h04.1 href hcur
  refine ⟨base', hb, η, hη, hηε, ?_⟩
  intro z hz hs
  have hzold := stateNeighborhood_mono S C hb hηε hz
  obtain ⟨τ, q, hτ, hq, hmap, hperiod, hqperiod, hreflect, hqreflect, hagree, _⟩ :=
    hqual z hzold hs
  obtain ⟨B, hB, hqB, hτB⟩ :=
    n04Realization_transport_C2_bounds hD hT hε hrefState h04 href hcur hzold hs hτ hq hagree
  have hratio := hratios z hz hs τ hτ.continuousOn hmap (fun m p hp => (hagree m p hp).1)
  have hC : 0 < B + Real.exp 1 := add_pos hB (Real.exp_pos _)
  have hBC : B ≤ B + Real.exp 1 := le_add_of_nonneg_right (Real.exp_pos _).le
  have hratioC (r : ℝ) (hr : r ∈ radialCore D) :
      Real.exp 1 ≤ (B + Real.exp 1) * T.E0 r :=
    (le_add_of_nonneg_left hB.le).trans (le_mul_of_one_le_right hC.le (hE0 r hr))
  refine ⟨τ, q, hτ, hq, hmap, hperiod, hqperiod, hreflect, hqreflect, hagree,
    B + Real.exp 1, 1, hC, zero_le_one, ?_, ?_, ?_, ?_⟩
  · intro p hp n hn
    rw [Real.rpow_one]
    exact (hqB p hp n hn).trans
      (mul_le_mul_of_nonneg_right hBC (zero_le_one.trans (hT.2.1 _ hp.1).2.2.2))
  · intro p hp n hn0 hn
    rw [Real.rpow_one]
    exact (hτB p hp n hn0 hn).trans
      (mul_le_mul_of_nonneg_right hBC (zero_le_one.trans (hT.2.1 _ hp.1).2.2.2))
  · intro p hp
    rw [Real.rpow_one]
    exact (hratio p hp).1.trans (hratioC p.1 hp.1)
  · intro p hp
    rw [Real.rpow_one]
    exact (hratio p hp).2.trans (hratioC p.1 hp.1)

end ContinuousFlexibility.Analysis
