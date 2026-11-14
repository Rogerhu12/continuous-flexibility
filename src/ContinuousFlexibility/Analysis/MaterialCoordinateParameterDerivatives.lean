module

public import ContinuousFlexibility.Analysis.MixedDerivativeHierarchy
public import ContinuousFlexibility.Analysis.MixedJetParameterDerivatives
public import ContinuousFlexibility.Analysis.MaterialRadiusJets

/-!
# Parameter differentiation after the actual material coordinate

The scalar chain rule has a finite expansion with coefficients depending
only on the fixed radius map. This exact formula commutes a parameter
derivative through every material mixed derivative. The input consists
of genuine ordinary mixed derivatives of the original spatial fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

def radialChainCoefficient (r : ℝ → ℝ) : (n : ℕ) → Fin (n + 1) → ℝ → ℝ
  | 0, _ => fun _ => 1
  | n + 1, j =>
      Fin.snoc (α := fun _ : Fin (n + 2) => ℝ → ℝ)
        (fun i : Fin (n + 1) => deriv (radialChainCoefficient r n i)) (fun _ => 0) j +
      Fin.cons (α := fun _ : Fin (n + 2) => ℝ → ℝ) (fun _ => 0)
        (fun i : Fin (n + 1) => fun x => radialChainCoefficient r n i x * deriv r x) j

theorem radialChainCoefficient_contDiff {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (n : ℕ) (i : Fin (n + 1)) :
    ContDiff ℝ ∞ (radialChainCoefficient r n i) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih =>
      let A : Fin (n + 1) → ℝ → ℝ := fun j => deriv (radialChainCoefficient r n j)
      let B : Fin (n + 1) → ℝ → ℝ :=
        fun j x => radialChainCoefficient r n j x * deriv r x
      have hA (j : Fin (n + 1)) : ContDiff ℝ ∞ (A j) :=
        (contDiff_infty_iff_deriv.mp (ih j)).2
      have hB (j : Fin (n + 1)) : ContDiff ℝ ∞ (B j) :=
        (ih j).mul (contDiff_infty_iff_deriv.mp hr).2
      have hl (j : Fin (n + 2)) : ContDiff ℝ ∞
          (Fin.snoc (α := fun _ : Fin (n + 2) => ℝ → ℝ) A (fun _ => 0) j) := by
        refine Fin.lastCases ?_ (fun l => ?_) j
        · simpa only [Fin.snoc_last] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
        · simpa only [Fin.snoc_castSucc] using hA l
      have ht (j : Fin (n + 2)) : ContDiff ℝ ∞
          (Fin.cons (α := fun _ : Fin (n + 2) => ℝ → ℝ) (fun _ => 0) B j) := by
        refine Fin.cases ?_ (fun l => ?_) j
        · simpa only [Fin.cons_zero] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
        · simpa only [Fin.cons_succ] using hB l
      exact (hl i).add (ht i)

theorem radialChainCoefficient_sum_succ (r : ℝ → ℝ)
    (n : ℕ) (x : ℝ) (v : ℕ → ℝ) :
    (∑ j : Fin (n + 2), radialChainCoefficient r (n + 1) j x * v j.val) =
      (∑ i : Fin (n + 1), deriv (radialChainCoefficient r n i) x * v i.val) +
      ∑ i : Fin (n + 1), radialChainCoefficient r n i x * deriv r x * v (i.val + 1) := by
  let A : Fin (n + 1) → ℝ → ℝ := fun i => deriv (radialChainCoefficient r n i)
  let B : Fin (n + 1) → ℝ → ℝ :=
    fun i x => radialChainCoefficient r n i x * deriv r x
  let L : Fin (n + 2) → ℝ → ℝ :=
    Fin.snoc (α := fun _ : Fin (n + 2) => ℝ → ℝ) A (fun _ => 0)
  let R : Fin (n + 2) → ℝ → ℝ :=
    Fin.cons (α := fun _ : Fin (n + 2) => ℝ → ℝ) (fun _ => 0) B
  have hl : (∑ j : Fin (n + 2), L j x * v j.val) =
      ∑ i : Fin (n + 1), deriv (radialChainCoefficient r n i) x * v i.val := by
    rw [Fin.sum_univ_castSucc]
    simp only [L, A, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, zero_mul, add_zero]
  have hr : (∑ j : Fin (n + 2), R j x * v j.val) =
      ∑ i : Fin (n + 1), radialChainCoefficient r n i x * deriv r x * v (i.val + 1) := by
    rw [Fin.sum_univ_succ]
    simp only [R, B, Fin.cons_zero, Fin.cons_succ, Fin.val_succ, zero_mul, zero_add]
  change (∑ j : Fin (n + 2), (L j x + R j x) * v j.val) = _
  simp only [add_mul, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hl hr

theorem mixedDerivative_comp_materialCoordinate_formula
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p =
      ∑ i : Fin (a + 1), radialChainCoefficient T.radius a i p.1 *
        mixedDerivative i.val b f (T.radius p.1, p.2) := by
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hinside (q : PolarPoint) : (T.radius q.1, q.2) ∈ annularOpen D :=
    ⟨(hT.2.2.2.2.2.2.2.1 q.1).1, mem_univ _⟩
  induction a generalizing p with
  | zero =>
      change iteratedDeriv b (fun θ => f (T.radius p.1, θ)) p.2 =
        ∑ i : Fin 1, radialChainCoefficient T.radius 0 i p.1 *
          mixedDerivative i.val b f (T.radius p.1, p.2)
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, radialChainCoefficient, one_mul,
        mixedDerivative, iteratedDeriv_zero]
  | succ a ih =>
      have heq : (fun x => mixedDerivative a b (fun q => f (T.radius q.1, q.2)) (x, p.2)) =
          (fun x => ∑ i : Fin (a + 1), radialChainCoefficient T.radius a i x *
            mixedDerivative i.val b f (T.radius x, p.2)) :=
        funext (fun x => ih (x, p.2))
      have hc (i : Fin (a + 1)) :
          HasDerivAt (radialChainCoefficient T.radius a i)
            (deriv (radialChainCoefficient T.radius a i) p.1) p.1 :=
        ((radialChainCoefficient_contDiff hr a i).differentiable (by simp) p.1).hasDerivAt
      have hm (i : Fin (a + 1)) :
          HasDerivAt (fun x => mixedDerivative i.val b f (T.radius x, p.2))
            (mixedDerivative (i.val + 1) b f (T.radius p.1, p.2) * deriv T.radius p.1) p.1 := by
        simpa only [Function.comp_def] using
          (mixedDerivative_hasDerivAt_radial hU hf i.val b (hinside p)).comp p.1
            ((hr.differentiable (by simp) p.1).hasDerivAt)
      have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (a + 1)))) =>
        (hc i).mul (hm i))
      have hderiv : deriv
          (fun x => ∑ i : Fin (a + 1), radialChainCoefficient T.radius a i x *
            mixedDerivative i.val b f (T.radius x, p.2)) p.1 =
          ∑ i : Fin (a + 1),
            (deriv (radialChainCoefficient T.radius a i) p.1 *
              mixedDerivative i.val b f (T.radius p.1, p.2) +
            radialChainCoefficient T.radius a i p.1 *
              (mixedDerivative (i.val + 1) b f (T.radius p.1, p.2) * deriv T.radius p.1)) :=
        hd.deriv
      have hsucc : mixedDerivative (a + 1) b (fun q => f (T.radius q.1, q.2)) p =
          deriv (fun x => mixedDerivative a b
            (fun q => f (T.radius q.1, q.2)) (x, p.2)) p.1 := by
        simp only [mixedDerivative, iteratedDeriv_succ]
      rw [hsucc, heq, hderiv]
      rw [radialChainCoefficient_sum_succ T.radius a p.1
        (fun j => mixedDerivative j b f (T.radius p.1, p.2))]
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem mixedJetHasDerivAt_comp_materialCoordinate
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {F : ℝ → PolarPoint → ℝ} {G : PolarPoint → ℝ} {t : ℝ}
    (hF : ∀ᶠ s in 𝓝 t, ContDiffOn ℝ ∞ (F s) (annularOpen D))
    (hG : ContDiffOn ℝ ∞ G (annularOpen D))
    (hderiv : ∀ a b : ℕ, ∀ p ∈ annularOpen D,
      HasDerivAt (fun s => mixedDerivative a b (F s) p) (mixedDerivative a b G p) t) :
    MixedJetHasDerivAt (fun s p => F s (T.radius p.1, p.2))
      (fun p => G (T.radius p.1, p.2)) t := by
  intro a b p
  have hp : (T.radius p.1, p.2) ∈ annularOpen D :=
    ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩
  rw [mixedDerivative_comp_materialCoordinate_formula hT hG a b p]
  have hd : HasDerivAt
      (fun s => ∑ i : Fin (a + 1), radialChainCoefficient T.radius a i p.1 *
        mixedDerivative i.val b (F s) (T.radius p.1, p.2))
      (∑ i : Fin (a + 1), radialChainCoefficient T.radius a i p.1 *
        mixedDerivative i.val b G (T.radius p.1, p.2)) t :=
    HasDerivAt.fun_sum (fun i _ => (hderiv i.val b _ hp).const_mul _)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hF] with s hs
  exact mixedDerivative_comp_materialCoordinate_formula hT hs a b p

end ContinuousFlexibility.Statements
