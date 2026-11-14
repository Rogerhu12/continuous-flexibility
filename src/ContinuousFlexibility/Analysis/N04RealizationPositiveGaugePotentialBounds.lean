module

public import ContinuousFlexibility.Analysis.N04RealizationPositiveGaugeHeightBounds
public import ContinuousFlexibility.Analysis.N04RealizationPotentialShiftedOneHigh

/-!
# The positive potential from the original root traces and principal fields

The two height inputs are constructed from the actual finite Taylor
height and the same supplied reference gauge. Their bounds are derived
before the three raw principal inputs enter the existing differential
product estimate. One multilinear normalization is applied to the actual
potential. The low order, parameter domain, and interpolation denominator
are unchanged. No potential estimate or CurrentJets premise is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_positiveGaugePotential_oneHigh
    (n K s shift : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ),
      ∀ U : Set X, IsOpen U → ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ h : X → Bool → PolarPoint → ℝ,
      (∀ y ∈ U, ∀ side θ, ContDiffAt ℝ ∞ (h y side) (if side then r else l, θ)) →
      (∀ y ∈ U, ∀ side θ, 0 < h y side (if side then r else l, θ)) →
      ∀ JH : ∀ side, ∀ j : ℕ, j ≤ n → ∀ u θ,
        SmoothDirections U (fun y => iteratedDeriv u
          (radialBoundaryJet (h y side) (if side then r else l) j) θ),
      ∀ Y H₀ : ℝ → ℝ, ContDiff ℝ ∞ (Function.invFun Y) →
        ContDiff ℝ ∞ H₀ → (∀ t, 0 < H₀ t) →
      ∀ τ σ : X → PolarPoint → PolarPoint,
        (∀ y ∈ U, Function.LeftInverse (σ y) (τ y)) →
      ∀ A : X → SymmetricCoefficients,
      ∀ RA : ∀ i : Fin 3, MixedJetRegularity U unitStrip
        (fun x => (![(A x).a, (A x).b, (A x).c] : Fin 3 → PolarPoint → ℝ) i),
      ∀ W M : ℝ, 0 ≤ W → W ≤ RH → 1 ≤ M → δ⁻¹ ≤ M →
      (∀ x ∈ U, p base (x - center) ≤ 1 → ∀ side θ,
        (h x side (if side then r else l, θ))⁻¹ ≤ M) →
      (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n, ∀ e : ℕ, e ≤ K →
        ∀ u : ℕ, u ≤ s + 2 → ∀ θ,
        ∀ x ∈ U, p base (x - center) ≤ 1 →
        ∀ v : Fin e → X, (∀ i, p base (v i) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
          (∀ i, p high (v i) ≤ R) →
        ‖(JH side j hj u θ).D e x v‖ ≤ M * parameterHeightWeight W e *
          R ^ (((u + shift * e : ℕ) : ℝ) /
            (((s + 2 + shift * K : ℕ) : ℝ) + 1))) →
      ∀ Mlow : ℝ, 0 ≤ Mlow →
      (∀ x ∈ U, p base (x - center) ≤ 1 → ∀ side j, 0 < j → j ≤ n → ∀ θ,
        |positiveHeightTaylorData l r (fun _ => 1) (h x) side j θ| ≤ Mlow) →
      ((n + 1 : ℕ) : ℝ) * Mlow * δ ≤ 1 →
      (∀ inv : Bool, ∀ q ∈ unitStrip, ∀ u w : ℕ, u + w ≤ s + 2 →
        |mixedDerivative u w
          (fun z : PolarPoint => if inv then (H₀ z.1)⁻¹ else H₀ z.1)
          (Function.invFun Y q.1, q.2)| ≤ M) →
      (∀ a : ℕ, a ≤ s + 2 → ∀ q ∈ unitStrip,
        (∑ i : Fin (a + 1), |radialChainCoefficient (Function.invFun Y) a i q.1|) ≤ M) →
      (∀ i : Fin 3, ∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s + 2 →
        ∀ q (hq : q ∈ unitStrip), ∀ x ∈ U, p base (x - center) ≤ 1 →
        ∀ v : Fin j → X, (∀ t, p base (v t) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
          (∀ t, p high (v t) ≤ R) →
        ‖((RA i).parameter u w q hq).D j x v‖ ≤ M * parameterHeightWeight W j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + 2 + shift * K : ℕ) : ℝ) + 1))) →
      let G : X → PolarPoint → ℝ := fun y q =>
        wholePositiveReferenceGaugeHeight (fun z => H₀ z.1) (σ y)
          (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y))
          (wholePositiveReferenceGaugeInverse (τ y) (positiveReferenceCylinderInverse Y) q)
      ∃ RP : MixedJetRegularity U unitStrip
        (fun x q => G x q * divergenceOperator (A x) (fun z => (G x z)⁻¹) q),
        ∀ k : ℕ, k ≤ K → 0 < k → ∀ a b : ℕ, a + b ≤ s →
        ∀ q (hq : q ∈ unitStrip), ∀ x ∈ U, p base (x - center) ≤ 1 →
        ∀ v : Fin k → X,
        ‖(RP.parameter a b q hq).D k x v‖ ≤ B * M ^ d * W *
          oneHighVariationWeight p base high (x - center) v := by
  classical
  let I : Type := Fin (K + 1) × Fin (s + 3) × Fin (s + 3)
  choose c d hc hd hb using fun i : I =>
    n04Realization_positiveGaugeHeight_shifted_parameter_bound (X := X)
      n i.1.val i.2.1.val i.2.2.val RH
  let C : ℝ := 1 + ∑ i : I, c i
  let D : ℕ := 1 + ∑ i : I, d i
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hc i)))
  have hD : 1 ≤ D := Nat.le_add_right _ _
  have hcC (i : I) : c i ≤ C :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdD (i : I) : d i ≤ D :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ _)
  obtain ⟨B₀, hB₀, hpotential⟩ :=
    n04Realization_potential_shifted_positive_oneHigh (X := X) K s shift RH
  refine ⟨1 + B₀ * C ^ 3, D * 3,
    le_add_of_nonneg_right (mul_nonneg hB₀.le (pow_nonneg (zero_le_one.trans hC) _)),
    by omega, ?_⟩
  intro p center base high U hU l r δ hδ hδ1 h hroot hpos JH Y H₀ hχ hH₀ hH₀pos
    τ σ hστ A RA W M hW hWR hM hδM hinv hrootJets Mlow hMlow hTaylor hsmall
    hfixed hchain hprincipal
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  let Q : X → PolarPoint → ℝ :=
    fun y => positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y)
  let height : X → PolarPoint → ℝ :=
    fun y => wholePositiveReferenceGaugeHeight (fun z => H₀ z.1) (σ y) (Q y)
  let inverse : X → PolarPoint → PolarPoint :=
    fun y => wholePositiveReferenceGaugeInverse (τ y) (positiveReferenceCylinderInverse Y)
  let G : X → PolarPoint → ℝ := fun y q => height y (inverse y q)
  let RQ : MixedJetRegularity U univ Q :=
    n04Realization_positiveHeightTaylor_mixedJetRegularity hU n l r δ
      h hroot hpos JH false
  have hQ : ∀ y ∈ U, ∀ q ∈ (univ : Set PolarPoint), 0 < Q y q := by
    intro y _ q _
    simp only [Q, positiveHeightTaylorInterpolation, one_mul]
    exact Real.exp_pos _
  let RG : MixedJetRegularity U unitStrip G ×
      MixedJetRegularity U unitStrip (fun y q => (G y q)⁻¹) :=
    n04Realization_positive_pulledHeight_regularity hU isOpen_Ioo isOpen_univ
      hχ (hH₀.comp contDiff_fst).contDiffOn (fun q _ => (hH₀pos q.1).ne') RQ hQ
      (fun _ _ _ => mem_univ _) hστ
      (fun y _ q => wholePositiveReferenceGaugeHeight_eq _ _ _ q)
      (fun y _ q => by
        simp only [inverse, wholePositiveReferenceGaugeInverse,
          Function.comp_apply, positiveReferenceCylinderInverse])
  let RP : MixedJetRegularity U unitStrip
      (fun x q => G x q * divergenceOperator (A x) (fun z => (G x z)⁻¹) q) :=
    RG.1.mul (n04Realization_mixedJetRegularity_divergence hU hΩ
      (RA 0) (RA 1) (RA 2) RG.2) hU hΩ
  let RF : ∀ i : Fin 5, MixedJetRegularity U unitStrip
      (fun x => n04RealizationPotentialInputs (A x) (G x) (fun q => (G x q)⁻¹) i) := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))))
    · exact RG.1
    · exact RA 0
    · exact RA 1
    · exact RA 2
    · exact RG.2
  have hraw : ∀ i : Fin 5, ∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s + 2 →
      ∀ q (hq : q ∈ unitStrip), ∀ x ∈ U, p base (x - center) ≤ 1 →
      ∀ v : Fin j → X, (∀ t, p base (v t) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R → (∀ t, p high (v t) ≤ R) →
      ‖((RF i).parameter u w q hq).D j x v‖ ≤
        C * M ^ (D : ℝ) * parameterHeightWeight W j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + 2 + shift * K : ℕ) : ℝ) + 1)) := by
    intro i j hj u w huw q hq x hx hlow v hv R hR hxR hvR
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    have htail : 0 ≤ parameterHeightWeight W j *
        R ^ (((u + w + shift * j : ℕ) : ℝ) /
          (((s + 2 + shift * K : ℕ) : ℝ) + 1)) :=
      mul_nonneg (parameterHeightWeight_nonneg hW j) (Real.rpow_nonneg hR0 _)
    have hheight (inv : Bool)
        (J : SmoothDirections U (fun y => mixedDerivative u w
          (fun z => if inv then (G y z)⁻¹ else G y z) q)) :
        ‖J.D j x v‖ ≤ C * M ^ (D : ℝ) * parameterHeightWeight W j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + 2 + shift * K : ℕ) : ℝ) + 1)) := by
      let t : I := (⟨j, Nat.lt_succ_of_le hj⟩, ⟨u, by omega⟩, ⟨w, by omega⟩)
      let P : X → Prop := fun z => p base z ≤ 1 ∧ p high z ≤ R
      have ht := hb t U hU l r δ hδ hδ1 h hroot hpos JH
        Y H₀ hχ hH₀ hH₀pos τ σ hστ x hx P v (fun t => ⟨hv t, hvR t⟩)
        W M R hW hWR hM hR hδM (s + 2 + shift * K) shift
        (hinv x hx hlow)
        (fun side d hd e he a ha θ z hz =>
          hrootJets side d hd e (he.trans hj) a (ha.trans huw) θ x hx hlow z
            (fun t => (hz t).1) R hR hxR (fun t => (hz t).2))
        Mlow hMlow (hTaylor x hx hlow) hsmall inv q hq
        (fun a b hab => hfixed inv q hq a b (hab.trans huw))
        (hchain u (by omega) q hq) J
      have hcoef : c t * M ^ d t ≤ C * M ^ D :=
        mul_le_mul (hcC t) (pow_le_pow_right₀ hM (hdD t))
          (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC)
      have ht' : ‖J.D j x v‖ ≤ c t * M ^ d t * parameterHeightWeight W j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + 2 + shift * K : ℕ) : ℝ) + 1)) := by
        simpa only [t] using ht
      simpa only [Real.rpow_natCast, mul_assoc] using
        ht'.trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef htail)
    have hprincipal' (t : Fin 3)
        (J : SmoothDirections U (fun y => mixedDerivative u w
          ((![(A y).a, (A y).b, (A y).c] : Fin 3 → PolarPoint → ℝ) t) q)) :
        ‖J.D j x v‖ ≤ C * M ^ (D : ℝ) * parameterHeightWeight W j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + 2 + shift * K : ℕ) : ℝ) + 1)) := by
      have heq := HasProjectiveJetsOn.unique hU J.hasProjectiveJetsOn
        ((RA t).parameter u w q hq).hasProjectiveJetsOn j x hx
      rw [heq]
      have hb := hprincipal t j hj u w huw q hq x hx hlow v hv R hR hxR hvR
      have hcoef : M ≤ C * M ^ D := by
        calc
          M = M ^ 1 := (pow_one M).symm
          _ ≤ M ^ D := pow_le_pow_right₀ hM hD
          _ ≤ C * M ^ D := le_mul_of_one_le_left
            (pow_nonneg (zero_le_one.trans hM) _) hC
      simpa only [Real.rpow_natCast, mul_assoc] using
        hb.trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef htail)
    fin_cases i
    · exact hheight false ((RF 0).parameter u w q hq)
    · exact hprincipal' 0 ((RF 1).parameter u w q hq)
    · exact hprincipal' 1 ((RF 2).parameter u w q hq)
    · exact hprincipal' 2 ((RF 3).parameter u w q hq)
    · exact hheight true ((RF 4).parameter u w q hq)
  refine ⟨RP, ?_⟩
  intro k hk hkpos a b hab q hq x hx hlow v
  have hbound := hpotential p center base high U hU unitStrip hΩ A G
    (fun x q => (G x q)⁻¹) RF (fun _ => W) (fun _ => M) C (D : ℝ) hC (by positivity)
    (fun _ _ => ⟨hW, hWR, hM⟩) hraw k hk hkpos a b hab q hq
    (RP.parameter a b q hq) x hx hlow v
  have hpow : M ^ ((D : ℝ) * 3) = M ^ (D * 3) := by
    rw [show (D : ℝ) * 3 = ((D * 3 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hpow] at hbound
  have htail : 0 ≤ M ^ (D * 3) * W *
      oneHighVariationWeight p base high (x - center) v :=
    mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) hW)
      (oneHighVariationWeight_nonneg p base high (x - center) v)
  calc
    _ ≤ B₀ * C ^ 3 * W * M ^ (D * 3) *
        oneHighVariationWeight p base high (x - center) v := hbound
    _ = (B₀ * C ^ 3) * (M ^ (D * 3) * W *
        oneHighVariationWeight p base high (x - center) v) := by ring
    _ ≤ (1 + B₀ * C ^ 3) * (M ^ (D * 3) * W *
        oneHighVariationWeight p base high (x - center) v) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) htail
    _ = _ := by ring

end ContinuousFlexibility.Analysis
