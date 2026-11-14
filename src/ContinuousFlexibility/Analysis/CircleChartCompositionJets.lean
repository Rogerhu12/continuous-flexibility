module

public import ContinuousFlexibility.Analysis.CircleAngularJetLinear
public import ContinuousFlexibility.Analysis.CircleAveragedComposition
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The actual parameter jets of circle chart composition

The chart parameter and the composed field are both allowed to vary.
The nth jet has one term differentiating the outer field n times and
one term for each slot differentiating its field component n-1 times.
All slots are represented by genuine multilinear maps; no formal jet
or assumed expansion is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

local instance circleChartCompositionJetsRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace
local instance circleChartCompositionJetsPairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleCompositionPhase (travel : ℕ → ℝ) (x : S.Space × S.Space)
    (m : ℕ) (θ : ℝ) : ℝ := θ + travel m + S.decode x.1 m θ

def circleCompositionScalarJet (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (n : ℕ) (x : S.Space × S.Space) (m : ℕ) (θ : ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => S.Space × S.Space) ℝ := by
  classical
  let H : (S.Space × S.Space) →ₗ[ℝ] ℝ :=
    (circleAngularJetEvaluationLinear hS 0 m θ).comp (LinearMap.fst ℝ S.Space S.Space)
  let V : (S.Space × S.Space) →ₗ[ℝ] ℝ :=
    (circleAngularJetEvaluationLinear hS (n - 1) m (circleCompositionPhase travel x m θ)).comp
      (LinearMap.snd ℝ S.Space S.Space)
  exact (iteratedDeriv n (S.decode x.2 m) (circleCompositionPhase travel x m θ)) •
      (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap (fun _ => H) +
    ∑ i : Fin n, (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap
      (fun j => if j = i then V else H)

def circleChartCompositionJets (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (n : ℕ) (x : S.Space × S.Space) :
    MultilinearMap ℝ (fun _ : Fin n => S.Space × S.Space) (ℕ → ℝ → ℝ) :=
  MultilinearMap.pi (fun m => MultilinearMap.pi
    (fun θ => circleCompositionScalarJet hS travel n x m θ))

theorem prod_single_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) (i : ι) (a : ℝ) :
    (∏ j, if j = i then a else h j) = a * ∏ j ∈ Finset.univ.erase i, h j := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if j = i then a else h j) (Finset.mem_univ i)]
  rw [if_pos rfl]
  congr 1
  exact Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))

theorem multilinear_mixed_product_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (a : ℝ) (H V : E →ₗ[ℝ] ℝ) (v : Fin n → E) :
    (a • (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap (fun _ => H) +
      ∑ i : Fin n, (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap
        (fun j => if j = i then V else H)) v =
      a * ∏ i, H (v i) + ∑ i : Fin n, V (v i) * ∏ j ∈ Finset.univ.erase i, H (v j) := by
  classical
  simp only [MultilinearMap.add_apply, MultilinearMap.smul_apply,
    MultilinearMap.sum_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← prod_single_replacement (fun j => H (v j)) i]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [ite_true]
  · simp only [if_neg hji]

theorem circleChartCompositionJets_apply (hS : IsCircleModel T γ S)
    (travel : ℕ → ℝ) (n : ℕ) (x : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) (m : ℕ) (θ : ℝ) :
    circleChartCompositionJets hS travel n x v m θ =
      iteratedDeriv n (S.decode x.2 m) (circleCompositionPhase travel x m θ) *
        ∏ i, S.decode (v i).1 m θ +
      ∑ i : Fin n, iteratedDeriv (n - 1) (S.decode (v i).2 m)
          (circleCompositionPhase travel x m θ) *
        ∏ j ∈ Finset.univ.erase i, S.decode (v j).1 m θ := by
  classical
  let H : (S.Space × S.Space) →ₗ[ℝ] ℝ :=
    (circleAngularJetEvaluationLinear hS 0 m θ).comp (LinearMap.fst ℝ S.Space S.Space)
  let V : (S.Space × S.Space) →ₗ[ℝ] ℝ :=
    (circleAngularJetEvaluationLinear hS (n - 1) m (circleCompositionPhase travel x m θ)).comp
      (LinearMap.snd ℝ S.Space S.Space)
  have h : circleCompositionScalarJet hS travel n x m θ v =
      iteratedDeriv n (S.decode x.2 m) (circleCompositionPhase travel x m θ) *
        ∏ i, H (v i) + ∑ i : Fin n, V (v i) * ∏ j ∈ Finset.univ.erase i, H (v j) :=
    multilinear_mixed_product_apply n
      (iteratedDeriv n (S.decode x.2 m) (circleCompositionPhase travel x m θ)) H V v
  change circleCompositionScalarJet hS travel n x m θ v = _
  simpa only [H, V, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    circleAngularJetEvaluationLinear_apply, iteratedDeriv_zero] using h

theorem circleChartCompositionJets_zero (hS : IsCircleModel T γ S)
    (travel : ℕ → ℝ) (x : S.Space × S.Space) :
    circleChartCompositionJets hS travel 0 x Fin.elim0 =
      fun m θ => S.decode x.2 m (circleCompositionPhase travel x m θ) := by
  funext m θ
  simp [circleChartCompositionJets_apply]

theorem circleAngularJetEvaluation_line (hS : IsCircleModel T γ S)
    (u v : S.Space) (n m : ℕ) (t θ : ℝ) :
    iteratedDeriv n (S.decode (u + t • v) m) θ =
      iteratedDeriv n (S.decode u m) θ + t * iteratedDeriv n (S.decode v m) θ := by
  have h := (circleAngularJetEvaluationLinear hS n m θ).map_add u (t • v)
  simpa only [map_smul, circleAngularJetEvaluationLinear_apply,
    RingHom.id_apply, smul_eq_mul] using h

theorem circleCompositionPhase_line (travel : ℕ → ℝ)
    (x w : S.Space × S.Space) (m : ℕ) (θ t : ℝ) :
    circleCompositionPhase travel (x + t • w) m θ =
      circleCompositionPhase travel x m θ + t * S.decode w.1 m θ := by
  change θ + travel m + S.decode (x.1 + t • w.1) m θ = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, RingHom.id_apply,
    smul_eq_mul, circleCompositionPhase]
  ring

theorem circleCompositionPhase_line_hasDerivAt (travel : ℕ → ℝ)
    (x w : S.Space × S.Space) (m : ℕ) (θ t : ℝ) :
    HasDerivAt (fun q : ℝ => circleCompositionPhase travel (x + q • w) m θ)
      (S.decode w.1 m θ) t := by
  have h := ((hasDerivAt_id t).mul_const (S.decode w.1 m θ)).const_add
    (circleCompositionPhase travel x m θ)
  simpa only [one_mul, id_eq, circleCompositionPhase_line] using h

theorem affine_outerJet_scalar_hasDerivAt
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (a d t : ℝ) :
    HasDerivAt (fun q : ℝ => iteratedDeriv n f (a + q * d) +
        q * iteratedDeriv n g (a + q * d))
      ((iteratedDeriv (n + 1) f (a + t * d) +
        t * iteratedDeriv (n + 1) g (a + t * d)) * d +
        iteratedDeriv n g (a + t * d)) t := by
  have hφ : HasDerivAt (fun q : ℝ => a + q * d) d t := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id t).mul_const d).const_add a
  have hcoef (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
      HasDerivAt (fun q : ℝ => iteratedDeriv n u (a + q * d))
        (iteratedDeriv (n + 1) u (a + t * d) * d) t := by
    have h := (hu.differentiable_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n)) (a + t * d)).hasDerivAt
    simpa only [iteratedDeriv_succ, Function.comp_def] using h.comp t hφ
  have h := (hcoef f hf).fun_add ((hasDerivAt_id t).fun_mul (hcoef g hg))
  convert h using 1 <;> simp only [id_eq, one_mul] <;> ring

theorem circleComposition_outerJet_line_eq
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (x w : S.Space × S.Space) (n m : ℕ) (θ q : ℝ) :
    iteratedDeriv n (S.decode (x + q • w).2 m)
        (circleCompositionPhase travel (x + q • w) m θ) =
      iteratedDeriv n (S.decode x.2 m)
          (circleCompositionPhase travel x m θ + q * S.decode w.1 m θ) +
        q * iteratedDeriv n (S.decode w.2 m)
          (circleCompositionPhase travel x m θ + q * S.decode w.1 m θ) := by
  change iteratedDeriv n (S.decode (x.2 + q • w.2) m) _ = _
  exact (circleAngularJetEvaluation_line hS x.2 w.2 n m q
    (circleCompositionPhase travel (x + q • w) m θ)).trans
    (congrArg (fun y : ℝ => iteratedDeriv n (S.decode x.2 m) y +
      q * iteratedDeriv n (S.decode w.2 m) y)
      (circleCompositionPhase_line travel x w m θ q))

/-- The coefficient of the all-chart-direction term has its ordinary
scalar derivative along every actual affine parameter line. -/
theorem circleComposition_outerJet_line_hasDerivAt
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (x w : S.Space × S.Space) (n m : ℕ) (θ t : ℝ) :
    HasDerivAt
      (fun q : ℝ => iteratedDeriv n (S.decode (x + q • w).2 m)
        (circleCompositionPhase travel (x + q • w) m θ))
      (iteratedDeriv (n + 1) (S.decode (x + t • w).2 m)
          (circleCompositionPhase travel (x + t • w) m θ) * S.decode w.1 m θ +
        iteratedDeriv n (S.decode w.2 m) (circleCompositionPhase travel (x + t • w) m θ)) t := by
  have h := affine_outerJet_scalar_hasDerivAt
    ((hS.2.2.2.1 x.2).1 m).1 ((hS.2.2.2.1 w.2).1 m).1 n
    (circleCompositionPhase travel x m θ) (S.decode w.1 m θ) t
  have hd := congrArg₂ (fun y z : ℝ => y * S.decode w.1 m θ + z)
    (circleComposition_outerJet_line_eq hS travel x w (n + 1) m θ t)
    (congrArg (iteratedDeriv n (S.decode w.2 m))
      (circleCompositionPhase_line travel x w m θ t))
  exact (h.congr_deriv hd.symm).congr_of_eventuallyEq
    (Eventually.of_forall (fun q => circleComposition_outerJet_line_eq hS travel x w n m θ q))

theorem fin_prod_erase_zero {n : ℕ} (h : Fin (n + 1) → ℝ) :
    (∏ j ∈ Finset.univ.erase (0 : Fin (n + 1)), h j) = ∏ i : Fin n, h i.succ := by
  have heq : (∏ j : Fin (n + 1), if j = 0 then (1 : ℝ) else h j) =
      ∏ i : Fin n, h i.succ := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.succ_ne_zero, ite_false, ite_true, one_mul]
  have hprod : (∏ j ∈ Finset.univ.erase (0 : Fin (n + 1)), h j) =
      ∏ j : Fin (n + 1), if j = 0 then (1 : ℝ) else h j := by
    simpa only [one_mul] using (prod_single_replacement h 0 (1 : ℝ)).symm
  exact hprod.trans heq

theorem fin_prod_erase_succ {n : ℕ} (h : Fin (n + 1) → ℝ) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i.succ, h j) =
      h 0 * ∏ j ∈ Finset.univ.erase i, h j.succ := by
  have heq : (∏ j : Fin (n + 1), if j = i.succ then (1 : ℝ) else h j) =
      h 0 * ∏ j ∈ Finset.univ.erase i, h j.succ := by
    rw [Fin.prod_univ_succ]
    simp only [show (0 : Fin (n + 1)) ≠ i.succ from (Fin.succ_ne_zero i).symm,
      if_false, Fin.succ_inj]
    rw [prod_single_replacement (fun j : Fin n => h j.succ) i (1 : ℝ), one_mul]
  have hprod : (∏ j ∈ Finset.univ.erase i.succ, h j) =
      ∏ j : Fin (n + 1), if j = i.succ then (1 : ℝ) else h j := by
    simpa only [one_mul] using (prod_single_replacement h i.succ (1 : ℝ)).symm
  exact hprod.trans heq

theorem circle_mixed_product_cons_algebra {n : ℕ}
    (A B d : ℝ) (p q : Fin n → ℝ) :
    A * (d * ∏ i, p i) +
        (B * ∏ i, p i + ∑ i, q i * (d * ∏ j ∈ Finset.univ.erase i, p j)) =
      (A * d + B) * ∏ i, p i +
        d * ∑ i, q i * ∏ j ∈ Finset.univ.erase i, p j := by
  classical
  rw [Finset.mul_sum]
  have hs : (∑ i, q i * (d * ∏ j ∈ Finset.univ.erase i, p j)) =
      ∑ i, d * (q i * ∏ j ∈ Finset.univ.erase i, p j) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs]
  ring

theorem circle_mul_sum_middle {ι : Type*} [Fintype ι]
    (d : ℝ) (p q : ι → ℝ) :
    d * (∑ i, p i * q i) = ∑ i, (p i * d) * q i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem circleChartCompositionJets_cons (hS : IsCircleModel T γ S)
    (travel : ℕ → ℝ) (n : ℕ) (x w : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) (m : ℕ) (θ : ℝ) :
    circleChartCompositionJets hS travel (n + 1) x (Fin.cons w v) m θ =
      (iteratedDeriv (n + 1) (S.decode x.2 m) (circleCompositionPhase travel x m θ) *
          S.decode w.1 m θ +
        iteratedDeriv n (S.decode w.2 m) (circleCompositionPhase travel x m θ)) *
          ∏ i, S.decode (v i).1 m θ +
      S.decode w.1 m θ *
        ∑ i : Fin n, iteratedDeriv n (S.decode (v i).2 m)
          (circleCompositionPhase travel x m θ) *
            ∏ j ∈ Finset.univ.erase i, S.decode (v j).1 m θ := by
  classical
  apply (circleChartCompositionJets_apply hS travel (n + 1) x (Fin.cons w v) m θ).trans
  simp only [Nat.add_sub_cancel, Fin.prod_univ_succ, Fin.sum_univ_succ,
    fin_prod_erase_zero, fin_prod_erase_succ, Fin.cons_zero, Fin.cons_succ]
  exact circle_mixed_product_cons_algebra
    (iteratedDeriv (n + 1) (S.decode x.2 m) (circleCompositionPhase travel x m θ))
    (iteratedDeriv n (S.decode w.2 m) (circleCompositionPhase travel x m θ))
    (S.decode w.1 m θ) (fun i => S.decode (v i).1 m θ)
    (fun i => iteratedDeriv n (S.decode (v i).2 m) (circleCompositionPhase travel x m θ))

/-- Every displayed parameter jet differentiates to the next displayed
jet along the actual affine parameter line. -/
theorem circleChartCompositionJets_line_hasDerivAt
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (n : ℕ) (x w : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) (m : ℕ) (θ t : ℝ) :
    HasDerivAt (fun q : ℝ => circleChartCompositionJets hS travel n (x + q • w) v m θ)
      (circleChartCompositionJets hS travel (n + 1) (x + t • w) (Fin.cons w v) m θ) t := by
  classical
  cases n with
  | zero =>
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    subst v
    simpa [circleChartCompositionJets_zero, circleChartCompositionJets_cons] using
      circleComposition_outerJet_line_hasDerivAt hS travel x w 0 m θ t
  | succ n =>
    let φ : ℝ → ℝ := fun q => circleCompositionPhase travel (x + q • w) m θ
    let P : ℝ := ∏ i, S.decode (v i).1 m θ
    let Q : Fin (n + 1) → ℝ :=
      fun i => ∏ j ∈ Finset.univ.erase i, S.decode (v j).1 m θ
    have hφ := circleCompositionPhase_line_hasDerivAt travel x w m θ t
    have hterm (i : Fin (n + 1)) :
        HasDerivAt (fun q => iteratedDeriv n (S.decode (v i).2 m) (φ q) * Q i)
          ((iteratedDeriv (n + 1) (S.decode (v i).2 m) (φ t) *
            S.decode w.1 m θ) * Q i) t := by
      have hc := (((hS.2.2.2.1 (v i).2).1 m).1.differentiable_iteratedDeriv
        n (by exact_mod_cast (ENat.natCast_lt_top n)) (φ t)).hasDerivAt
      have hd := (hc.comp t hφ).mul_const (Q i)
      simpa only [iteratedDeriv_succ, Function.comp_def] using hd
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
    have hmain := (circleComposition_outerJet_line_hasDerivAt hS travel x w (n + 1) m θ t).mul_const P
    have h := hmain.fun_add hsum
    convert h using 1
    · funext q
      simp only [circleChartCompositionJets_apply, Nat.add_sub_cancel, P, Q, φ]
    · apply (circleChartCompositionJets_cons hS travel (n + 1) (x + t • w) w v m θ).trans
      dsimp only [P, Q, φ]
      exact congrArg (fun z : ℝ =>
        (iteratedDeriv (n + 2) (S.decode (x + t • w).2 m)
            (circleCompositionPhase travel (x + t • w) m θ) * S.decode w.1 m θ +
          iteratedDeriv (n + 1) (S.decode w.2 m)
            (circleCompositionPhase travel (x + t • w) m θ)) *
          (∏ i, S.decode (v i).1 m θ) + z)
        (circle_mul_sum_middle (S.decode w.1 m θ)
          (fun i => iteratedDeriv (n + 1) (S.decode (v i).2 m)
            (circleCompositionPhase travel (x + t • w) m θ))
          (fun i => ∏ j ∈ Finset.univ.erase i, S.decode (v j).1 m θ))

theorem circleCompositionPhase_contDiff (hS : IsCircleModel T γ S)
    (travel : ℕ → ℝ) (x : S.Space × S.Space) (m : ℕ) :
    ContDiff ℝ ∞ (circleCompositionPhase travel x m) :=
  (contDiff_id.add contDiff_const).add ((hS.2.2.2.1 x.1).1 m).1

theorem circleCompositionPhase_period (hS : IsCircleModel T γ S)
    (travel : ℕ → ℝ) (x : S.Space × S.Space) (m : ℕ) (θ : ℝ) :
    circleCompositionPhase travel x m (θ + Real.pi) =
      circleCompositionPhase travel x m θ + Real.pi := by
  simp only [circleCompositionPhase, ((hS.2.2.2.1 x.1).1 m).2 θ]
  ring

theorem circleChartCompositionJets_contDiff (hS : IsCircleModel T γ S)
    (travel : ℕ → ℝ) (n : ℕ) (x : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) (m : ℕ) :
    ContDiff ℝ ∞ (circleChartCompositionJets hS travel n x v m) := by
  classical
  have hφ := circleCompositionPhase_contDiff hS travel x m
  have hu (u : S.Space) (b : ℕ) : ContDiff ℝ ∞ (iteratedDeriv b (S.decode u m)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv b ((hS.2.2.2.1 u).1 m).1
  have heq : circleChartCompositionJets hS travel n x v m =
      (fun θ => iteratedDeriv n (S.decode x.2 m) (circleCompositionPhase travel x m θ) *
        ∏ i, S.decode (v i).1 m θ +
      ∑ i : Fin n, iteratedDeriv (n - 1) (S.decode (v i).2 m)
          (circleCompositionPhase travel x m θ) *
        ∏ j ∈ Finset.univ.erase i, S.decode (v j).1 m θ) := by
    funext θ
    exact circleChartCompositionJets_apply hS travel n x v m θ
  rw [heq]
  apply ContDiff.add
  · exact ((hu x.2 n).comp hφ).mul
      (contDiff_prod (fun i _ => ((hS.2.2.2.1 (v i).1).1 m).1))
  · exact ContDiff.sum (fun i _ => ((hu (v i).2 (n - 1)).comp hφ).mul
      (contDiff_prod (fun j _ => ((hS.2.2.2.1 (v j).1).1 m).1)))

theorem circleChartCompositionJets_periodic (hS : IsCircleModel T γ S)
    (travel : ℕ → ℝ) (n : ℕ) (x : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) (m : ℕ) :
    Function.Periodic (circleChartCompositionJets hS travel n x v m) Real.pi := by
  classical
  have hp (u : S.Space) (b : ℕ) :
      Function.Periodic (iteratedDeriv b (S.decode u m)) Real.pi :=
    circlePeriodic_iteratedDeriv_real ((hS.2.2.2.1 u).1 m).2 b
  have hv (u : S.Space) : Function.Periodic (S.decode u m) Real.pi :=
    ((hS.2.2.2.1 u).1 m).2
  have hp' (u : S.Space) (b : ℕ) (t : ℝ) :
      iteratedDeriv b (S.decode u m) (t + Real.pi) = iteratedDeriv b (S.decode u m) t :=
    hp u b t
  have hv' (u : S.Space) (t : ℝ) : S.decode u m (t + Real.pi) = S.decode u m t := hv u t
  intro θ
  simp only [circleChartCompositionJets_apply, circleCompositionPhase_period hS, hp', hv']

end ContinuousFlexibility.Statements
