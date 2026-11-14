module

public import ContinuousFlexibility.Analysis.SmoothDirectionsLocalJointAngular

/-!
# Uniform seminorm bounds for the actual local joint towers

The finite joint expansion has the exact product bound obtained by
replacing each direction by the sum of its parameter seminorm and its
spatial absolute value. Only finitely many input jet orders enter each
output order. Consequently the seminorm and constant remain uniform in
any additional spatial label, such as the circle angle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem scalarAngularExpansion_seminorm_bound
    (n : ℕ) (p : Seminorm ℝ E) (A : ScalarAngularJetData E) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ a k, a + k ≤ n → ∀ v : Fin k → E,
      |A a k v| ≤ C * ∏ i, p (v i))
    (v : Fin n → E × ℝ) :
    |scalarAngularExpansion n A v| ≤ C * ∏ i, (p (v i).1 + |(v i).2|) := by
  induction n generalizing A C with
  | zero =>
      simpa only [scalarAngularExpansion_zero_apply, Fin.prod_univ_zero, mul_one] using
        hA 0 0 (by omega) Fin.elim0
  | succ n ih =>
      have hhead (a k : ℕ) (hak : a + k ≤ n) (u : Fin k → E) :
          |scalarAngularHead A (v 0) a k u| ≤
            (C * p (v 0).1) * ∏ i, p (u i) := by
        simpa only [scalarAngularHead_apply, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ, mul_assoc] using
          hA a (k + 1) (by omega) (Fin.cons (v 0).1 u)
      have hshift (a k : ℕ) (hak : a + k ≤ n) (u : Fin k → E) :
          |scalarAngularShift A a k u| ≤ C * ∏ i, p (u i) :=
        hA (a + 1) k (by omega) u
      have hh := ih (scalarAngularHead A (v 0))
        (mul_nonneg hC (apply_nonneg p (v 0).1)) hhead (Fin.tail v)
      have hs := ih (scalarAngularShift A) hC hshift (Fin.tail v)
      rw [scalarAngularExpansion_succ_apply]
      calc
        _ ≤ |scalarAngularExpansion n (scalarAngularHead A (v 0)) (Fin.tail v)| +
            |(v 0).2| * |scalarAngularExpansion n (scalarAngularShift A) (Fin.tail v)| := by
          simpa only [abs_mul] using abs_add_le
            (scalarAngularExpansion n (scalarAngularHead A (v 0)) (Fin.tail v))
            ((v 0).2 * scalarAngularExpansion n (scalarAngularShift A) (Fin.tail v))
        _ ≤ (C * p (v 0).1) * ∏ i, (p (Fin.tail v i).1 + |(Fin.tail v i).2|) +
            |(v 0).2| * (C * ∏ i, (p (Fin.tail v i).1 + |(Fin.tail v i).2|)) :=
          add_le_add hh (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
        _ = _ := by rw [Fin.prod_univ_succ]; simp only [Fin.tail]; ring

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

private theorem joint_scalar_bound_mono
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

private theorem uniform_scalar_jets_finite_label_orders
    {ι : Type*} {U : Set E} {f : ℕ → ι → E → ℝ}
    (J : ∀ a i, SmoothDirections U (f a i))
    (hbound : ∀ a, UniformScalarJetSeminormBounds (J a)) (s k : ℕ) :
    ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ a ≤ s, ∀ i x, x ∈ U → ∀ v : Fin k → E,
        |(J a i).D k x v| ≤ B * (1 + p x) * ∏ j, p (v j) := by
  induction s with
  | zero =>
      obtain ⟨p, B, hp, hB, hb⟩ := hbound 0 k
      refine ⟨p, B, hp, hB, ?_⟩
      intro a ha i x hx v
      have heq : a = 0 := by omega
      subst a
      exact hb i x hx v
  | succ s ih =>
      obtain ⟨p, B, hp, hB, hb⟩ := ih
      obtain ⟨q, A, hq, hA, ha⟩ := hbound (s + 1) k
      have hpq : p ≤ p + q := fun x => le_add_of_nonneg_right (apply_nonneg q x)
      have hqp : q ≤ p + q := fun x => le_add_of_nonneg_left (apply_nonneg p x)
      refine ⟨p + q, B + A, hp.add hq, add_nonneg hB hA, ?_⟩
      intro a has i x hx v
      by_cases hle : a ≤ s
      · exact (hb a hle i x hx v).trans
          (joint_scalar_bound_mono p (p + q) hpq hB (le_add_of_nonneg_right hA) x v)
      · have heq : a = s + 1 := by omega
        subst a
        exact (ha i x hx v).trans
          (joint_scalar_bound_mono q (p + q) hqp hA (le_add_of_nonneg_left hB) x v)

theorem uniformScalarJetSeminormBounds_finite_rectangle
    {ι : Type*} {U : Set E} {f : ℕ → ι → E → ℝ}
    (J : ∀ a i, SmoothDirections U (f a i))
    (hbound : ∀ a, UniformScalarJetSeminormBounds (J a)) (s n : ℕ) :
    ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ a ≤ s, ∀ k ≤ n, ∀ i x, x ∈ U → ∀ v : Fin k → E,
        |(J a i).D k x v| ≤ B * (1 + p x) * ∏ j, p (v j) := by
  induction n with
  | zero =>
      obtain ⟨p, B, hp, hB, hb⟩ := uniform_scalar_jets_finite_label_orders J hbound s 0
      refine ⟨p, B, hp, hB, ?_⟩
      intro a ha k hk i x hx v
      have heq : k = 0 := by omega
      subst k
      exact hb a ha i x hx v
  | succ n ih =>
      obtain ⟨p, B, hp, hB, hb⟩ := ih
      obtain ⟨q, A, hq, hA, ha⟩ := uniform_scalar_jets_finite_label_orders J hbound s (n + 1)
      have hpq : p ≤ p + q := fun x => le_add_of_nonneg_right (apply_nonneg q x)
      have hqp : q ≤ p + q := fun x => le_add_of_nonneg_left (apply_nonneg p x)
      refine ⟨p + q, B + A, hp.add hq, add_nonneg hB hA, ?_⟩
      intro a has k hkn i x hx v
      by_cases hle : k ≤ n
      · exact (hb a has k hle i x hx v).trans
          (joint_scalar_bound_mono p (p + q) hpq hB (le_add_of_nonneg_right hA) x v)
      · have heq : k = n + 1 := by omega
        subst k
        exact (ha a has i x hx v).trans
          (joint_scalar_bound_mono q (p + q) hqp hA (le_add_of_nonneg_left hB) x v)

theorem uniformScalarJetSeminormBounds_local_joint
    {ι : Type*} {U : Set E} {V : Set ℝ} {f : ℕ → ι → ℝ → E → ℝ}
    (J : ∀ a i r, r ∈ V → SmoothDirections U (f a i r))
    (hU : IsOpen U) (hc : Convex ℝ U) (hV : IsOpen V)
    (hf : ∀ a i x, x ∈ U → ContinuousOn (fun r => f a i r x) V)
    (hbound : ∀ a, UniformScalarJetSeminormBounds
      (fun ir : ι × V => J a ir.1 ir.2 ir.2.property))
    (hderiv : ∀ a i r, r ∈ V → ∀ x, x ∈ U →
      HasDerivAt (fun t => f a i t x) (f (a + 1) i r x) r)
    (K : ∀ i, SmoothDirections (U ×ˢ V) (fun z : E × ℝ => f 0 i z.2 z.1)) :
    UniformScalarJetSeminormBounds K := by
  intro n
  obtain ⟨p, B, hp, hB, hb⟩ := uniformScalarJetSeminormBounds_finite_rectangle
    (fun a (ir : ι × V) => J a ir.1 ir.2 ir.2.property) hbound n n
  let q : Seminorm ℝ (E × ℝ) := pairGrading (fun _ => p) realGrading 0
  have hqapply (z : E × ℝ) : q z = p z.1 + |z.2| := by
    change p z.1 + ‖z.2‖ = _
    rw [Real.norm_eq_abs]
  have hq : Continuous q := by
    have heq : (q : (E × ℝ) → ℝ) = fun z => p z.1 + |z.2| := funext hqapply
    rw [heq]
    exact (hp.comp continuous_fst).add continuous_snd.abs
  refine ⟨q, B, hq, hB, ?_⟩
  intro i z hz v
  let hi (a : ℕ) : UniformScalarJetSeminormBounds (fun r : V => J a i r r.property) :=
    (hbound a).reindex (fun r : V => (i, r))
  let L := localAngularTowerJointDirectionsOfUniform (fun a r hr => J a i r hr)
    hU hc hV (fun a => hf a i) hi (fun a => hderiv a i)
  have hsame : (K i).D n z v =
      scalarAngularExpansion n
        (fun a k => (localScalarJetMap (fun r hr => J a i r hr) k z.1 z.2).toMultilinearMap) v := by
    exact congrArg (fun A : (E × ℝ) [×n]→L[ℝ] ℝ => A v) ((K i).unique L n z hz)
  rw [hsame]
  have hC : 0 ≤ B * (1 + p z.1) :=
    mul_nonneg hB (add_nonneg zero_le_one (apply_nonneg p z.1))
  have hinput (a k : ℕ) (hak : a + k ≤ n) (u : Fin k → E) :
      |(localScalarJetMap (fun r hr => J a i r hr) k z.1 z.2).toMultilinearMap u| ≤
        (B * (1 + p z.1)) * ∏ j, p (u j) := by
    change |localScalarJetMap (fun r hr => J a i r hr) k z.1 z.2 u| ≤ _
    rw [localScalarJetMap_apply, localScalarJet_of_mem _ k z.1 u hz.2]
    exact hb a (by omega) k (by omega) (i, ⟨z.2, hz.2⟩) z.1 hz.1 u
  have hestimate := scalarAngularExpansion_seminorm_bound n p _ hC hinput v
  simp only [← hqapply] at hestimate
  apply hestimate.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun j _ => apply_nonneg q (v j)))
  apply mul_le_mul_of_nonneg_left _ hB
  rw [hqapply]
  linarith only [abs_nonneg z.2]

end ContinuousFlexibility.Analysis
