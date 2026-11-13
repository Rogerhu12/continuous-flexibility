import ContinuousFlexibility.Analysis.N04NegativeChartFieldPrefix
import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
import ContinuousFlexibility.Analysis.N04NegativeChartRootFlowFactory
import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# The actual coefficient prefixes on their finite state representatives

Taking state derivatives first and spatial derivatives second gives the
same genuine jets. Thus the constructed representatives inherit the
sharp coefficient bounds on the physical half. Only the two spatial
coordinates contribute to the operator-norm constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X P : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- A true state derivative of the chosen smooth representative. -/
def negativeChartCoefficientJet (d : P × PolarPoint → ℝ) (k : ℕ)
    (v : Fin k → P) (p : PolarPoint) : ℝ :=
  iteratedFDeriv ℝ k d (0, p) (fun i => (v i, (0 : PolarPoint)))

theorem negativeChartCoefficientJet_contDiff {d : P × PolarPoint → ℝ}
    (hd : ContDiff ℝ ∞ d) (k : ℕ) (v : Fin k → P) :
    ContDiff ℝ ∞ (negativeChartCoefficientJet d k v) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P × PolarPoint) ℝ
    (fun i => (v i, (0 : PolarPoint)))).contDiff.comp
      ((hd.iteratedFDeriv_right (m := ∞) (i := k) (by simp)).comp
        (contDiff_const.prodMk contDiff_id))

private theorem representative_mixedJet_eq
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    (RF : MixedJetRegularity U Ω f) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (x : X) (hx : x ∈ U) (L : P →L[ℝ] X)
    {d : P × PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d)
    {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (heq : ∀ y ∈ V, ∀ p ∈ Ω, d (y, p) = f (x + L y) p)
    (k a b : ℕ) (v : Fin k → P) {q : PolarPoint} (hq : q ∈ Ω) :
    mixedDerivative a b (negativeChartCoefficientJet d k v) q =
      (RF.parameter a b q hq).D k x (fun i => L (v i)) := by
  let J : SmoothDirections ((univ : Set P) ×ˢ (univ : Set PolarPoint)) d :=
    smoothDirectionsOfJets (isOpen_univ.prod isOpen_univ)
      (fun n => iteratedFDeriv ℝ n d)
      (hasProjectiveJetsOn_of_contDiffOn (isOpen_univ.prod isOpen_univ) hd.contDiffOn)
  let Q := (n04Realization_jointMixedRegularity J isOpen_univ isOpen_univ
    (convex_univ.prod convex_univ)).parameter a b q (mem_univ _)
  let U₀ : Set P := V ∩ (fun y => x + L y) ⁻¹' U
  have hU₀ : IsOpen U₀ := hV.inter (hU.preimage (continuous_const.add L.continuous))
  have h0₀ : (0 : P) ∈ U₀ := ⟨h0, by simpa only [map_zero, add_zero] using hx⟩
  let A := (smoothDirections_precompAffine (RF.parameter a b q hq) x L).restrict
    hU₀ (fun _ h => h.2)
  let B : SmoothDirections U₀ (fun y => mixedDerivative a b (fun p => d (y, p)) q) :=
    A.congrOn (fun y hy =>
      (mixedDerivative_congr_on_open hΩ (fun p hp => heq y hy.1 p hp) a b hq).symm)
  have he := congrArg (fun T : P [×k]→L[ℝ] ℝ => T v)
    ((Q.restrict hU₀ (subset_univ _)).unique B k 0 h0₀)
  have he' : Q.D k 0 v = (RF.parameter a b q hq).D k x (fun i => L (v i)) := by
    simpa only [B, A, SmoothDirections.congrOn, SmoothDirections.restrict_D,
      smoothDirections_precompAffine_D_apply, map_zero, add_zero] using he
  have hm := n04Realization_mixedParameter_eq_joint J isOpen_univ isOpen_univ
    (convex_univ.prod convex_univ) a b k (0 : P) (mem_univ _) q (mem_univ _) Q v
  exact hm.symm.trans he'

/-- The bound is charged only for the two spatial coordinates; arbitrary
finite state directions have already been evaluated in the same tower. -/
theorem n04NegativeChart_representative_spatialJet_le
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    (RF : MixedJetRegularity U Ω f) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (x : X) (hx : x ∈ U) (L : P →L[ℝ] X)
    {d : P × PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d)
    {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (heq : ∀ y ∈ V, ∀ p ∈ Ω, d (y, p) = f (x + L y) p)
    (k j : ℕ) (v : Fin k → P) {q : PolarPoint} (hq : q ∈ Ω)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ a b, a + b = j → ‖(RF.parameter a b q hq).D k x (fun i => L (v i))‖ ≤ M) :
    ‖iteratedFDeriv ℝ j (negativeChartCoefficientJet d k v) q‖ ≤ (2 : ℝ) ^ j * M := by
  apply norm_iteratedFDeriv_le_of_mixedDerivative hΩ
    (negativeChartCoefficientJet_contDiff hd k v).contDiffOn j hq hM
  intro a b hab
  rw [representative_mixedJet_eq RF hU hΩ x hx L hd hV h0 heq k a b v hq]
  exact hb a b hab

/-- The fixed first-spatial prefix is inherited by every genuine finite
representative. Its state weight and fractional spatial degree are literal. -/
theorem N04NegativeChartFirstSpatialBounds.representative_prefix
    {I : Type*} {p : ℕ → Seminorm ℝ X} {center : X} {base K shift : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {H E : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (hb : N04NegativeChartFirstSpatialBounds p center base U Ω H E f K shift)
    (RF : ∀ i, MixedJetRegularity U (Ω i) (f i))
    (hU : IsOpen U) (hΩ : ∀ i, IsOpen (Ω i))
    (hH : ∀ i q, q ∈ Ω i → 0 ≤ H i q) (hE : ∀ i q, q ∈ Ω i → 1 ≤ E i q)
    (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ i k, k ≤ K → ∀ j, j ≤ s + 1 →
      ∀ x ∈ U, p base (x - center) ≤ 1 → ∀ L : P →L[ℝ] X,
      ∀ d : P × PolarPoint → ℝ, ContDiff ℝ ∞ d →
      ∀ V : Set P, IsOpen V → (0 : P) ∈ V →
        (∀ y ∈ V, ∀ q ∈ Ω i, d (y, q) = f i (x + L y) q) →
      ∀ v : Fin k → P, (∀ a, p base (L (v a)) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (base + s + shift * K + 1) (x - center) ≤ R →
        (∀ a, p (base + s + shift * K + 1) (L (v a)) ≤ R) →
      ∀ q ∈ Ω i, ‖iteratedFDeriv ℝ j (negativeChartCoefficientJet d k v) q‖ ≤
        B * E i q ^ B * parameterHeightWeight (H i q) k *
          R ^ (((j - 1 + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  obtain ⟨C, hC, hc⟩ := hb s
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack ((2 : ℝ) ^ (s + 1) * C) C
  refine ⟨B, hB, ?_⟩
  intro i k hk j hj x hx hlow L d hd V hV h0 heq v hv R hR hxR hvR q hq
  let M : ℝ := C * E i q ^ C * parameterHeightWeight (H i q) k *
    R ^ (((j - 1 + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans (hE i q hq)) _))
      (parameterHeightWeight_nonneg (hH i q hq) k)) (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hjet := n04NegativeChart_representative_spatialJet_le
    (RF i) hU (hΩ i) x hx L hd hV h0 heq k j v hq hM
    (fun a b hab => by
      have hh := hc i k hk a b (hab.trans_le hj) q hq
        ((RF i).parameter a b q hq) x hx hlow (fun a => L (v a)) hv R hR hxR hvR
      simpa only [hab] using hh)
  have ht : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (s + 1) := pow_le_pow_right₀ (by norm_num) hj
  calc
    _ ≤ (2 : ℝ) ^ j * M := hjet
    _ ≤ (2 : ℝ) ^ (s + 1) * M := mul_le_mul_of_nonneg_right ht hM
    _ = (((2 : ℝ) ^ (s + 1) * C) * E i q ^ C) * parameterHeightWeight (H i q) k *
        R ^ (((j - 1 + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
      dsimp only [M]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpack (E i q) (hE i q hq))
        (parameterHeightWeight_nonneg (hH i q hq) k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

namespace N04RealizationStart

/-- The coefficient estimate in the actual finite state coordinates.
The full-half sample is fixed throughout the spatial fiber. -/
def negativeHalfFiniteCoefficientBounds (W : N04RealizationStart)
    (e : ℕ ≃ N04PieceIndex W.D) (base domainBase K shift : ℕ)
    (f : (AnnularState W.S × ℝ) → ℕ → Bool → PolarPoint → ℝ) : Prop :=
  ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m side k, k ≤ K → ∀ j, j ≤ s + 1 →
    ∀ x ∈ stateNeighborhood W.S W.C domainBase W.negativeHalfStateRadius,
      pairGrading (stateGrading W.S) realGrading base (x - (W.C.referenceState, 0)) ≤ 1 →
    ∀ L : P →L[ℝ] (AnnularState W.S × ℝ),
    ∀ d : P × PolarPoint → ℝ, ContDiff ℝ ∞ d →
    ∀ V : Set P, IsOpen V → (0 : P) ∈ V →
      (∀ y ∈ V, ∀ q ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth m side) ×ˢ univ,
        d (y, q) = f (x + L y) m side q) →
    ∀ v : Fin k → P,
      (∀ a, pairGrading (stateGrading W.S) realGrading base (L (v a)) ≤ 1) →
    ∀ R : ℝ, 1 ≤ R →
      pairGrading (stateGrading W.S) realGrading (base + s + shift * K + 1)
        (x - (W.C.referenceState, 0)) ≤ R →
      (∀ a, pairGrading (stateGrading W.S) realGrading (base + s + shift * K + 1)
        (L (v a)) ≤ R) →
    ∀ q ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth m side) ×ˢ univ,
      ‖iteratedFDeriv ℝ j (negativeChartCoefficientJet d k v) q‖ ≤
        B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
          parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((j - 1 + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {F : NegativeOpticalFactors W e} {base loss : ℕ}

/-- Both actual coefficients inherit their already proved fixed base
bounds on every representative supplied by the root-flow factory. -/
theorem FullHalfFieldPowerControl.finiteRepresentative_prefix
    (A : F.FullHalfFieldPowerControl base loss) :
    ∃ base' : ℕ, base ≤ base' ∧ ∀ K : ℕ, ∃ shift : ℕ,
      W.negativeHalfFiniteCoefficientBounds (P := P) e base' base K shift F.fullHalfDrift ∧
      W.negativeHalfFiniteCoefficientBounds (P := P) e base' base K shift F.fullHalfSpeed := by
  obtain ⟨base', hb, hp⟩ := A.firstSpatial_prefix
  refine ⟨base', hb, fun K => ?_⟩
  obtain ⟨shift, hd, hc⟩ := hp K
  have hH (i : ℕ × Bool) (q : PolarPoint)
      (_hq : q ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ) :
      0 ≤ W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hE (i : ℕ × Bool) (q : PolarPoint)
      (_hq : q ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ) :
      1 ≤ W.T.E0 (W.negativeHalfSample e i.1 i.2) := W.floor _
  have hdrift := hd.representative_prefix A.1.regular
    (isOpen_stateNeighborhood W.S W.C base W.negativeHalfStateRadius)
    (fun _ => isOpen_Ioo.prod isOpen_univ) hH hE
  have hspeed := hc.representative_prefix A.2.regular
    (isOpen_stateNeighborhood W.S W.C base W.negativeHalfStateRadius)
    (fun _ => isOpen_Ioo.prod isOpen_univ) hH hE
  refine ⟨shift, ?_, ?_⟩
  · intro s
    obtain ⟨B, hB, hbound⟩ := hdrift s
    exact ⟨B, hB, fun m side => hbound (m, side)⟩
  · intro s
    obtain ⟨B, hB, hbound⟩ := hspeed s
    exact ⟨B, hB, fun m side => hbound (m, side)⟩

end NegativeOpticalFactors
end N04RealizationStart

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04NegativeChartFirstSpatialBounds.representative_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04NegativeChartFirstSpatialBounds.representative_prefix

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.finiteRepresentative_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.finiteRepresentative_prefix
