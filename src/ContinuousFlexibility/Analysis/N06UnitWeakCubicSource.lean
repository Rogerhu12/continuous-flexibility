import ContinuousFlexibility.Analysis.N06UnitWeakGraphData
import ContinuousFlexibility.Analysis.N06WeakCubicLimit
import ContinuousFlexibility.Analysis.N06CubicMultiplierJets
import ContinuousFlexibility.Analysis.N06WeakJetProduct

/-!
# The actual cubic source on a completed canonical cylinder

The same five graph limits give both the distributional cubic divergence
and all of its angular weak jets in the original canonical L2 row. Matching
reflection signs make the source even. The scalar graph constant and the
fixed-order multiplication constant are kept explicit throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {Kc : CanonicalData S} {m b : ℕ}
  {a c V : ℝ → ℝ}
  {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)} {K : ℝ}

/-- The retained modal representatives identify the five completed graph
fields with the actual cubic divergence against every original test. -/
theorem N06UnitWeakGraphData.cubic_pairing
    (P : N06UnitWeakGraphData a c V U F K)
    (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (hUeven : (fun p : PolarPoint => U 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (U 0 : PolarPoint → ℝ))
    (hUjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (U 0) (U k) k.val)
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hC : ContDiffOn ℝ ∞ C (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hpA : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), A (p + (0, Real.pi)) = A p)
    (hpB : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), B (p + (0, Real.pi)) = B p)
    (hpC : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), C (p + (0, Real.pi)) = C p)
    (hφ : CanonicalTest S Kc m φ) :
    (∫ p, U 0 p *
      divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
        ∂canonicalMeasure S Kc m) =
      ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p *
          P.field i 0 p) * φ p ∂canonicalMeasure S Kc m := by
  exact n06_canonical_weak_cubic_pairing_of_graph_limits hl hr
    (fun k => U k) hUeven hUjets P.modes
    (fun i => (P.representative i).contDiffOne)
    (fun i => (P.representative i).firstAC)
    (fun i => (P.representative i).memLp)
    (fun i => (P.representative i).firstMemLp)
    (fun i => (P.representative i).secondMemLp)
    (fun i => (P.representative i).ae_eq)
    (fun N i => P.cutMemLp N 0 i) (fun i => P.field i 0)
    (fun i => P.cut_tendsto 0 i) hA hB hC hpA hpB hpC hφ

/-- The genuine weak cubic divergence belongs to the original finite
canonical jet row, is even, and satisfies the complete reference graph
bound. No bounded operator or regularity of the source is assumed. -/
theorem N06UnitWeakGraphData.cubic_source
    (P : N06UnitWeakGraphData a c V U F K)
    (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (hUeven : (fun p : PolarPoint => U 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (U 0 : PolarPoint → ℝ))
    (hUjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (U 0) (U k) k.val)
    {A B C : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hC : ContDiffOn ℝ ∞ C (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hpA : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), A (p + (0, Real.pi)) = A p)
    (hpB : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), B (p + (0, Real.pi)) = B p)
    (hpC : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), C (p + (0, Real.pi)) = C p)
    (heA : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), A (p.1, Real.pi - p.2) = A p)
    (hoB : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), B (p.1, Real.pi - p.2) = -B p)
    (heC : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), C (p.1, Real.pi - p.2) = C p)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ j k : ℕ, j + k ≤ b + 1 →
      ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
        |mixedDerivative j k A p| ≤ δ ∧ |mixedDerivative j k B p| ≤ δ ∧
          |mixedDerivative j k C p| ≤ δ) :
    ∃ R : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m),
      (∀ k, WeakCanonicalAngularDerivative S Kc m (R 0) (R k) k.val) ∧
      ((fun p : PolarPoint => R 0 (p.1, Real.pi - p.2))
        =ᵐ[canonicalMeasure S Kc m] (R 0 : PolarPoint → ℝ)) ∧
      ((R 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S Kc m] fun p =>
        ∑ i : Fin 5,
          n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p *
            P.field i 0 p) ∧
      (∀ φ, CanonicalTest S Kc m φ →
        (∫ p, U 0 p *
          divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
            ∂canonicalMeasure S Kc m) =
          ∫ p, R 0 p * φ p ∂canonicalMeasure S Kc m) ∧
      ‖R‖ ≤ 5 * n06WeakAngularMultiplierCost b * δ * (∑ i : Fin 5, ‖P.field i‖) ∧
      ‖R‖ ^ 2 ≤ 2048000 * n06WeakAngularMultiplierCost b ^ 2 * K ^ 10 * δ ^ 2 *
        (‖F‖ ^ 2 + ‖U‖ ^ 2) := by
  classical
  let M : Fin 5 → PolarPoint → ℝ :=
    n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C
  have hstrip : canonicalOpen S Kc m = Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    simp only [canonicalOpen, hl, hr]
  have hd : ContDiff ℝ ∞ cylinderWeight := by
    change ContDiff ℝ ∞ (fun r : ℝ => r * (1 - r))
    exact contDiff_id.mul (contDiff_const.sub contDiff_id)
  have he : ContDiff ℝ ∞ (fun r : ℝ => 1 - 2 * r) :=
    contDiff_const.sub (contDiff_const.mul contDiff_id)
  have hpos (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : 0 < cylinderWeight r :=
    mul_pos hr.1 (sub_pos.mpr hr.2)
  have hM (i : Fin 5) : ContDiffOn ℝ ∞ (M i) (canonicalOpen S Kc m) := by
    rw [hstrip]
    exact n06CubicGraphMultipliers_contDiffOn_strip
      hd.contDiffOn he.contDiffOn hpos hA hB hC i
  have hMp (i : Fin 5) (p : PolarPoint) (hp : p ∈ canonicalOpen S Kc m) :
      M i (p + (0, Real.pi)) = M i p := by
    rw [hstrip] at hp
    exact n06CubicGraphMultipliers_periodicOn_strip _ _
      (fun q hq => hpA q ⟨hq, mem_univ _⟩)
      (fun q hq => hpB q ⟨hq, mem_univ _⟩)
      (fun q hq => hpC q ⟨hq, mem_univ _⟩) i p hp.1
  have hMe (i : Fin 5) (p : PolarPoint) (hp : p ∈ canonicalOpen S Kc m) :
      M i (p.1, Real.pi - p.2) = n06CubicGraphParity i * M i p := by
    rw [hstrip] at hp
    exact n06CubicGraphMultipliers_reflectionOn_strip _ _ hA hB hC
      (fun q hq => heA q ⟨hq, mem_univ _⟩)
      (fun q hq => hoB q ⟨hq, mem_univ _⟩)
      (fun q hq => heC q ⟨hq, mem_univ _⟩) i p hp.1
  have hMb (i : Fin 5) (k : ℕ) (hk : k ≤ b)
      (p : PolarPoint) (hp : p ∈ canonicalOpen S Kc m) :
      |mixedDerivative 0 k (M i) p| ≤ 5 * δ := by
    rw [hstrip] at hp
    have hpIcc : p.1 ∈ Icc (0 : ℝ) 1 := ⟨hp.1.1.le, hp.1.2.le⟩
    have he₁ : |1 - 2 * p.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩
    exact n06CubicGraphMultipliers_angularJet_abs_leOn_strip _ _ hA hB hC hδ p hp.1
      (cylinderWeight_nonneg hpIcc) (cylinderWeight_le_one hpIcc) he₁
      (fun j k hjk => hcoeff j k hjk p hp) k hk i
  let J : Fin 5 → PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m) :=
    fun i => n06CanonicalJetMultiply (M i) (hM i) (5 * δ) (hMb i) (P.field i)
  let R : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m) := ∑ i, J i
  have hRapply (k : Fin (b + 1)) : R k = ∑ i, J i k := by
    simpa only [Finset.sum_apply] using congrFun
      (WithLp.ofLp_sum (p := 2) (V := Fin (b + 1) → CanonicalL2 S Kc m) Finset.univ J) k
  have hJweak (i : Fin 5) (k : Fin (b + 1)) :
      WeakCanonicalAngularDerivative S Kc m (J i 0) (J i k) k.val :=
    n06CanonicalJetMultiply_weak (M i) (hM i) (hMp i) (5 * δ) (hMb i)
      (P.field i) (P.weakAngular i) k
  have hJeven (i : Fin 5) :
      (fun p : PolarPoint => J i 0 (p.1, Real.pi - p.2))
        =ᵐ[canonicalMeasure S Kc m] (J i 0 : PolarPoint → ℝ) :=
    n06CanonicalJetMultiply_sameParity (M i) (hM i)
      (n06CubicGraphParity i) (n06CubicGraphParity_sq i) (hMe i)
      (5 * δ) (hMb i) (P.field i) (P.reflection i)
  have hRsum : (R 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S Kc m]
      fun p => ∑ i, J i 0 p := by
    rw [hRapply]
    exact Lp.coeFn_fun_finsetSum Finset.univ (fun i => J i 0)
  have hRbase : (R 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S Kc m]
      fun p => ∑ i, M i p * P.field i 0 p := by
    refine hRsum.trans ?_
    have hsum := eventuallyEq_sum (s := Finset.univ) (fun i _ =>
      n06CanonicalJetMultiply_zero_ae (M i) (hM i) (5 * δ) (hMb i) (P.field i))
    filter_upwards [hsum] with p hp
    simpa only [Finset.sum_apply] using hp
  have hRnorm : ‖R‖ ≤ 5 * n06WeakAngularMultiplierCost b * δ *
      (∑ i : Fin 5, ‖P.field i‖) := by
    calc
      _ ≤ ∑ i, ‖J i‖ := norm_sum_le _ _
      _ ≤ ∑ i, n06WeakAngularMultiplierCost b * (5 * δ) * ‖P.field i‖ :=
        Finset.sum_le_sum (fun i _ => n06CanonicalJetMultiply_norm_le
          (M i) (hM i) (5 * δ) (by positivity) (hMb i) (P.field i))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  refine ⟨R, ?_, ?_, hRbase, ?_, hRnorm, ?_⟩
  · intro k
    rw [hRapply, hRapply]
    exact WeakCanonicalAngularDerivative.n06_sum Finset.univ (fun i _ => hJweak i k)
  · have hsum := eventuallyEq_sum (s := Finset.univ) (fun i _ => hJeven i)
    have hreflect := n06_measurePreserving_canonicalAngularReflection.quasiMeasurePreserving.ae_eq_comp
      hRsum
    filter_upwards [hreflect, hRsum, hsum] with p hr hs he
    have hr' : R 0 (p.1, Real.pi - p.2) = ∑ i, J i 0 (p.1, Real.pi - p.2) := by
      simpa only [Function.comp_apply] using hr
    rw [hr', hs]
    simpa only [Finset.sum_apply] using he
  · intro φ hφ
    refine (P.cubic_pairing hl hr hUeven hUjets hA hB hC hpA hpB hpC hφ).trans ?_
    apply integral_congr_ae
    filter_upwards [hRbase] with p hp
    rw [hp]
  · have hsum : (∑ i : Fin 5, ‖P.field i‖) ^ 2 ≤ 5 * ∑ i : Fin 5, ‖P.field i‖ ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_ofNat] using
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 5))
          (fun _ => (1 : ℝ)) (fun i => ‖P.field i‖)
    have hcost : 0 ≤ n06WeakAngularMultiplierCost b := n06WeakAngularMultiplierCost_nonneg b
    calc
      ‖R‖ ^ 2 ≤ (5 * n06WeakAngularMultiplierCost b * δ *
          (∑ i : Fin 5, ‖P.field i‖)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hRnorm
      _ = (5 * n06WeakAngularMultiplierCost b * δ) ^ 2 *
          (∑ i : Fin 5, ‖P.field i‖) ^ 2 := mul_pow _ _ 2
      _ ≤ (5 * n06WeakAngularMultiplierCost b * δ) ^ 2 *
          (5 * ∑ i : Fin 5, ‖P.field i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = (125 * n06WeakAngularMultiplierCost b ^ 2 * δ ^ 2) *
          (∑ i : Fin 5, ‖P.field i‖ ^ 2) := by ring
      _ ≤ (125 * n06WeakAngularMultiplierCost b ^ 2 * δ ^ 2) *
          (16384 * K ^ 10 * (‖F‖ ^ 2 + ‖U‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left P.norm_sq_bound (by positivity)
      _ = _ := by ring

end ContinuousFlexibility.Analysis
