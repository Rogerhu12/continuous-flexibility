import ContinuousFlexibility.Analysis.CircleSingleComponent
import ContinuousFlexibility.Analysis.CircleJetAssembly
import ContinuousFlexibility.Analysis.SmoothDirectionsAngularJets

/-!
# Genuine circle towers for one varying radial component

A scalar angular family with genuine parameter towers is realized in
the existing circle space after placing it in a single component. The
weighted energy sum is finite. This gives local spatial regularity of
inverse compositions without extending the uniform endpoint theory to
a new family of circle models.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : ℕ → ℝ → E → ℝ}

private theorem scalar_jet_bound_mono
    (p q : Seminorm ℝ E) (hpq : p ≤ q) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    {n : ℕ} (x : E) (v : Fin n → E) :
    A * (1 + p x) * ∏ i, p (v i) ≤ B * (1 + q x) * ∏ i, q (v i) := by
  have hprod : (∏ i, p (v i)) ≤ ∏ i, q (v i) :=
    Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun i _ => hpq (v i))
  exact mul_le_mul
    (mul_le_mul hAB (add_le_add (le_refl (1 : ℝ)) (hpq x))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (hA.trans hAB))
    hprod (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
    (mul_nonneg (hA.trans hAB) (add_nonneg zero_le_one (apply_nonneg _ _)))

theorem uniformScalarJetSeminormBounds_finite_orders
    (J : ∀ b θ, SmoothDirections U (f b θ))
    (hbound : ∀ b, UniformScalarJetSeminormBounds (J b)) (n s : ℕ) :
    ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ b ≤ s, ∀ θ x, x ∈ U → ∀ v : Fin n → E,
        |(J b θ).D n x v| ≤ B * (1 + p x) * ∏ i, p (v i) := by
  induction s with
  | zero =>
    obtain ⟨p, B, hp, hB, hb⟩ := hbound 0 n
    refine ⟨p, B, hp, hB, ?_⟩
    intro b hbs θ x hx v
    have heq : b = 0 := by omega
    subst b
    exact hb θ x hx v
  | succ s ih =>
    obtain ⟨p, B, hp, hB, hb⟩ := ih
    obtain ⟨q, A, hq, hA, ha⟩ := hbound (s + 1) n
    have hpq : p ≤ p + q := fun x => by
      change p x ≤ p x + q x
      exact le_add_of_nonneg_right (apply_nonneg _ _)
    have hqp : q ≤ p + q := fun x => by
      change q x ≤ p x + q x
      exact le_add_of_nonneg_left (apply_nonneg _ _)
    refine ⟨p + q, B + A, hp.add hq, add_nonneg hB hA, ?_⟩
    intro b hbs θ x hx v
    by_cases hb' : b ≤ s
    · exact (hb b hb' θ x hx v).trans
        (scalar_jet_bound_mono p (p + q) hpq hB (le_add_of_nonneg_right hA) x v)
    · have heq : b = s + 1 := by omega
      subst b
      exact (ha θ x hx v).trans
        (scalar_jet_bound_mono q (p + q) hqp hA (le_add_of_nonneg_left hB) x v)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators ENNReal

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {S : CircleModelData} {U : Set E}
  {f : ℕ → ℝ → E → ℝ}
  (J : ∀ b θ, SmoothDirections U (f b θ))
  (hU : IsOpen U) (hc : Convex ℝ U)
  (hbound : ∀ b, UniformScalarJetSeminormBounds (J b))
  (hangular : ∀ b θ x, x ∈ U →
    HasDerivAt (fun ψ => f b ψ x) (f (b + 1) θ x) θ)
  (hperiod : ∀ x ∈ U, Function.Periodic (fun θ => f 0 θ x) Real.pi)
  (m : ℕ)

def singleComponentScalarJets (n : ℕ) (x : E) :
    MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ) :=
  (circleSingleComponentFieldLinear m).compMultilinearMap
    (MultilinearMap.pi (fun θ => ((J 0 θ).D n x).toMultilinearMap))

theorem singleComponentScalarJets_apply (n : ℕ) (x : E) (v : Fin n → E) :
    singleComponentScalarJets J m n x v =
      circleSingleComponentField m (fun θ => (J 0 θ).D n x v) := rfl

include hU hc hbound hangular

theorem singleComponentScalarJets_iteratedDeriv
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (i b : ℕ) (θ : ℝ) :
    iteratedDeriv b (singleComponentScalarJets J m n x v i) θ =
      if i = m then (J b θ).D n x v else 0 := by
  rw [singleComponentScalarJets_apply, circleSingleComponentField_iteratedDeriv]
  have hd := smoothDirections_angular_jet_iteratedDeriv J hU hc hbound hangular n 0 b x hx v θ
  have hindex := congrArg (fun k : ℕ => (J k θ).D n x v) (Nat.zero_add b)
  exact congrArg (fun t : ℝ => if i = m then t else 0) (hd.trans hindex)

include hperiod in
theorem singleComponentScalarJets_member
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    CircleMember T γ (singleComponentScalarJets J m n x v) := by
  rw [singleComponentScalarJets_apply]
  apply circleSingleComponentField_member T γ m _
    (smoothDirections_angular_jet_contDiff J hU hc hbound hangular n 0 x hx v)
  intro θ
  have heq := (J 0 (θ + Real.pi)).unique
    ((J 0 θ).congrOn (fun y hy => (hperiod y hy θ).symm)) n x hx
  exact congrArg (fun A : E [×n]→L[ℝ] ℝ => A v) heq

theorem singleComponentScalarJets_normBounds
    (hM : ∀ i, 0 ≤ T.M (T.sample i)) (hH : ∀ i, 0 ≤ T.H (T.sample i)) :
    CircleJetNormBounds (T := T) (γ := γ) (U := U) (singleComponentScalarJets J m) := by
  intro n s
  obtain ⟨p, B, hp, hB, hb⟩ := uniformScalarJetSeminormBounds_finite_orders J hbound n s
  let C : ℝ := Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) * Real.pi) *
    (max 1 (T.M (T.sample m))) ^ s * T.H (T.sample m) ^ (-γ)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
    (Real.rpow_nonneg (hH m) _)
  refine ⟨p, C * B, hp, mul_nonneg hC hB, ?_⟩
  intro x hx v
  rw [singleComponentScalarJets_apply]
  have hpos : 0 ≤ B * (1 + p x) * ∏ i, p (v i) :=
    mul_nonneg (mul_nonneg hB (add_nonneg zero_le_one (apply_nonneg _ _)))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  have h := circleSingleComponentField_norm_le (γ := γ) hM hH m s _
    (smoothDirections_angular_jet_contDiff J hU hc hbound hangular n 0 x hx v) hpos
    (fun b hbs θ => by
      rw [smoothDirections_angular_jet_iteratedDeriv J hU hc hbound hangular n 0 b x hx v θ,
        Nat.zero_add]
      exact hb b hbs θ x hx v)
  exact h.trans_eq (by dsimp only [C]; ring)

theorem singleComponentScalarJets_hasDerivAt
    (n : ℕ) (x w : E) (v : Fin n → E) (t : ℝ) (ht : x + t • w ∈ U)
    (i b : ℕ) (θ : ℝ) :
    HasDerivAt (fun s => iteratedDeriv b (singleComponentScalarJets J m n (x + s • w) v i) θ)
      (iteratedDeriv b (singleComponentScalarJets J m (n + 1) (x + t • w)
        (Fin.cons w v) i) θ) t := by
  have hline : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
      (hU.mem_nhds ht)
  by_cases hi : i = m
  · subst i
    rw [singleComponentScalarJets_iteratedDeriv J hU hc hbound hangular m
      (n + 1) _ ht _ m b θ, if_pos rfl]
    apply ((J b θ).hasDerivAt_line_jet x w n v ht).congr_of_eventuallyEq
    filter_upwards [hline] with s hs
    simp only [singleComponentScalarJets_iteratedDeriv J hU hc hbound hangular m n _ hs,
      if_pos rfl, ite_true]
  · rw [singleComponentScalarJets_iteratedDeriv J hU hc hbound hangular m
      (n + 1) _ ht _ i b θ, if_neg hi]
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [hline] with s hs
    simp only [singleComponentScalarJets_iteratedDeriv J hU hc hbound hangular m n _ hs,
      if_neg hi]

theorem singleComponentScalarJets_secondEnvelopes
    (hM : ∀ i, 0 ≤ T.M (T.sample i)) (hH : ∀ i, 0 ≤ T.H (T.sample i)) :
    CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U) (singleComponentScalarJets J m) := by
  intro n x hx v w
  have hcont : Continuous (fun t : ℝ => x + t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hline : {t : ℝ | x + t • w ∈ U} ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simpa only [zero_smul, add_zero] using hx))
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hline
  have hmem : ∀ t : ℝ, |t| < min δ 1 → x + t • w ∈ U := by
    intro t ht
    apply hδU
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht.trans_le (min_le_left δ 1)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, hmem, ?_⟩
  intro s
  obtain ⟨p, B, hp, hB, hb⟩ := uniformScalarJetSeminormBounds_finite_orders J hbound (n + 2) s
  let energy : ℕ → ℝ≥0∞ := fun i => if i = m then 1 else 0
  let W : ℝ := (max 1 (T.M (T.sample m))) ^ s * T.H (T.sample m) ^ (-γ)
  let vs : Fin (n + 2) → E := Fin.cons w (Fin.cons w v)
  let A : ℝ := B * (1 + p x + p w) * ∏ i, p (vs i)
  have hW : 0 ≤ W := mul_nonneg
    (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.rpow_nonneg (hH m) _)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg hB (by positivity)) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  have hE : (∑' i, energy i) = 1 := by
    rw [tsum_eq_single m (fun i hi => by simp only [energy, if_neg hi])]
    simp only [energy, if_pos rfl]
  refine ⟨energy, W * A, ?_, mul_nonneg hW hA, ?_⟩
  · rw [hE]
    exact ENNReal.one_lt_top
  · intro t ht i b k hbk θ
    rw [singleComponentScalarJets_iteratedDeriv J hU hc hbound hangular m
      (n + 2) _ (hmem t ht) _ i b θ]
    by_cases hi : i = m
    · subst i
      simp only [if_pos rfl, energy, ENNReal.toReal_one, Real.sqrt_one, mul_one]
      have hk : T.M (T.sample m) ^ k ≤ (max 1 (T.M (T.sample m))) ^ s :=
        (pow_le_pow_left₀ (hM m) (le_max_right _ _) k).trans
          (pow_le_pow_right₀ (le_max_left _ _) (by omega))
      have hpaffine : p (x + t • w) ≤ p x + p w := by
        have hts : |t| ≤ 1 := (ht.trans_le (min_le_right δ 1)).le
        calc
          p (x + t • w) ≤ p x + p (t • w) := map_add_le_add _ _ _
          _ = p x + |t| * p w := by rw [map_smul_eq_mul, Real.norm_eq_abs]
          _ ≤ p x + p w := add_le_add le_rfl
            (mul_le_of_le_one_left (apply_nonneg _ _) hts)
      have hjet : |(J b θ).D (n + 2) (x + t • w) vs| ≤ A :=
        (hb b (by omega) θ _ (hmem t ht) vs).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith only [hpaffine]) hB)
            (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)))
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (hH m) _))
        hjet (abs_nonneg _) hW
    · simp only [if_neg hi, abs_zero, mul_zero, energy, ENNReal.toReal_zero, Real.sqrt_zero,
        le_refl]

include hperiod in
theorem exists_singleComponent_circle_smoothDirections
    (hS : IsCircleModel T γ S)
    (hM : ∀ i, 0 ≤ T.M (T.sample i)) (hH : ∀ i, 0 ≤ T.H (T.sample i))
    (F : E → S.Space)
    (hF : ∀ x ∈ U, S.decode (F x) = circleSingleComponentField m (fun θ => f 0 θ x)) :
    ∃ K : SmoothDirections U F, ∀ n x, x ∈ U → ∀ v : Fin n → E,
      S.decode (K.D n x v) = singleComponentScalarJets J m n x v := by
  apply exists_circle_smoothDirections_of_scalar_jets hS hM hH hU hc F
    (singleComponentScalarJets J m)
    (singleComponentScalarJets_member J hU hc hbound hangular hperiod m)
    (singleComponentScalarJets_normBounds J hU hc hbound hangular m hM hH)
  · intro x hx
    rw [hF x hx, singleComponentScalarJets_apply]
    congr 1
    funext θ
    exact (J 0 θ).zero x hx
  · exact singleComponentScalarJets_hasDerivAt J hU hc hbound hangular m
  · exact singleComponentScalarJets_secondEnvelopes J hU hc hbound hangular m hM hH

end ContinuousFlexibility.Statements
