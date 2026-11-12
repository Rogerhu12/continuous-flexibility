import ContinuousFlexibility.Analysis.BoundaryMixedJets
import ContinuousFlexibility.Analysis.BoundaryJetClosure
import ContinuousFlexibility.Analysis.PointwiseCylinderJets
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite ordinary jets at the closed edge of a smooth strip

Each equality is first proved on the actual open strip and then passed
to its boundary using continuity of the particular finite derivative.
No common neighborhood of infinite smoothness is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem closedStrip_mem_closure {a b : ℝ} (hab : a < b)
    {p : PolarPoint} (hp : p.1 ∈ Icc a b) :
    p ∈ closure (Ioo a b ×ˢ (univ : Set ℝ)) := by
  rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
  exact ⟨hp, mem_univ _⟩

private theorem continuousAt_eq_of_eqOn_of_mem_closure
    {E : Type*} [TopologicalSpace E] {F G : E → ℝ} {U : Set E} {p : E}
    (hF : ContinuousAt F p) (hG : ContinuousAt G p)
    (he : EqOn F G U) (hp : p ∈ closure U) : F p = G p := by
  apply sub_eq_zero.mp
  exact (hF.sub hG).continuousWithinAt.eq_const_of_mem_closure hp
    (fun q hq => sub_eq_zero.mpr (he hq))

theorem iteratedDeriv_radialBoundaryJet_eq_mixedDerivative_on_closedStrip
    {F : PolarPoint → ℝ} {a b c : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc : c ∈ Icc a b) (hFc : ∀ θ, ContDiffAt ℝ ∞ F (c, θ))
    (i j : ℕ) (θ : ℝ) :
    iteratedDeriv j (radialBoundaryJet F c i) θ =
      mixedDerivative i j F (c, θ) := by
  have hleft : ContinuousAt
      (fun p : PolarPoint => iteratedDeriv j (radialBoundaryJet F p.1 i) p.2)
      (c, θ) :=
    (contDiffAt_angularSliceJet (contDiffAt_radialSliceJet (hFc θ) i) j).continuousAt
  have hright : ContinuousAt (mixedDerivative i j F) (c, θ) :=
    (contDiffAt_mixedDerivative (hFc θ) i j).continuousAt
  apply continuousAt_eq_of_eqOn_of_mem_closure hleft hright ?_
    (closedStrip_mem_closure hab hc)
  intro p hp
  exact iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
    (isOpen_Ioo.prod isOpen_univ) hF p.1
    (fun η => ⟨hp.1, mem_univ η⟩) i j p.2

theorem iteratedFDeriv_cylinderBasis_eq_mixedDerivative_on_closedStrip
    {F : PolarPoint → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    {p : PolarPoint} (hp : p.1 ∈ Icc a b) (hFp : ContDiffAt ℝ ∞ F p)
    (n : ℕ) (w : Fin n → Fin 2) :
    iteratedFDeriv ℝ n F p (fun i => cylinderBasisVector (w i)) =
      mixedDerivative (∑ i, if w i = 0 then 1 else 0)
        (∑ i, if w i = 0 then 0 else 1) F p := by
  have hjet : ContinuousAt (iteratedFDeriv ℝ n F) p :=
    (hFp.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)).continuousAt
  have hleft : ContinuousAt
      (fun q => iteratedFDeriv ℝ n F q (fun i => cylinderBasisVector (w i))) p :=
    (continuous_eval_const (fun i => cylinderBasisVector (w i))).continuousAt.comp hjet
  have hright := (contDiffAt_mixedDerivative hFp
    (∑ i, if w i = 0 then 1 else 0) (∑ i, if w i = 0 then 0 else 1)).continuousAt
  exact continuousAt_eq_of_eqOn_of_mem_closure hleft hright
    (fun _ hq => iteratedFDeriv_cylinderBasis_eq_mixedDerivative
      (isOpen_Ioo.prod isOpen_univ) hF n hq w)
    (closedStrip_mem_closure hab hp)

private theorem multilinear_eq_of_cylinder_words {n : ℕ}
    (A B : PolarPoint [×n]→L[ℝ] ℝ)
    (h : ∀ w : Fin n → Fin 2,
      A (fun i => cylinderBasisVector (w i)) =
        B (fun i => cylinderBasisVector (w i))) : A = B := by
  classical
  let coord : PolarPoint → Fin 2 → ℝ := fun v j => if j = 0 then v.1 else v.2
  have hsum (v : PolarPoint) :
      (∑ j : Fin 2, coord v j • cylinderBasisVector j) = v := by
    rw [Fin.sum_univ_two]
    ext <;> simp [coord, cylinderBasisVector]
  have hexpand (T : PolarPoint [×n]→L[ℝ] ℝ) (v : Fin n → PolarPoint) :
      T v = ∑ w : Fin n → Fin 2, (∏ i, coord (v i) (w i)) •
        T (fun i => cylinderBasisVector (w i)) := by
    have hv : (fun i : Fin n => ∑ j : Fin 2, coord (v i) j • cylinderBasisVector j) = v :=
      funext (fun i => hsum (v i))
    have he := T.toMultilinearMap.map_sum
      (fun i : Fin n => fun j : Fin 2 => coord (v i) j • cylinderBasisVector j)
    change T (fun i => ∑ j : Fin 2, coord (v i) j • cylinderBasisVector j) =
      ∑ w : Fin n → Fin 2, T (fun i => coord (v i) (w i) • cylinderBasisVector (w i)) at he
    simpa only [hv, ContinuousMultilinearMap.map_smul_univ] using he
  ext v
  rw [hexpand A v, hexpand B v]
  apply Finset.sum_congr rfl
  intro w _
  rw [h w]

theorem iteratedFDeriv_eq_of_radialBoundaryJets_eq_on_closedStrip
    {F G : PolarPoint → ℝ} {a b c : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hG : ContDiffOn ℝ ∞ G (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc : c ∈ Icc a b)
    (hFc : ∀ θ, ContDiffAt ℝ ∞ F (c, θ))
    (hGc : ∀ θ, ContDiffAt ℝ ∞ G (c, θ)) {N : ℕ}
    (hjet : ∀ j, j ≤ N → ∀ θ,
      radialBoundaryJet F c j θ = radialBoundaryJet G c j θ)
    {k : ℕ} (hk : k ≤ N) (θ : ℝ) :
    iteratedFDeriv ℝ k F (c, θ) = iteratedFDeriv ℝ k G (c, θ) := by
  classical
  apply multilinear_eq_of_cylinder_words
  intro w
  rw [iteratedFDeriv_cylinderBasis_eq_mixedDerivative_on_closedStrip hab hF hc (hFc θ),
    iteratedFDeriv_cylinderBasis_eq_mixedDerivative_on_closedStrip hab hG hc (hGc θ)]
  have hcount :
      (∑ i, if w i = 0 then 1 else 0) + (∑ i, if w i = 0 then 0 else 1) = k := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin k, (1 : ℕ) := Finset.sum_congr rfl (fun i _ => by
        by_cases hi : w i = 0 <;> simp only [hi, ite_true, ite_false, zero_add, add_zero])
      _ = k := by simp
  have hrad : (∑ i, if w i = 0 then 1 else 0) ≤ N := by omega
  rw [← iteratedDeriv_radialBoundaryJet_eq_mixedDerivative_on_closedStrip
    hab hF hc hFc, ← iteratedDeriv_radialBoundaryJet_eq_mixedDerivative_on_closedStrip
    hab hG hc hGc, funext (hjet _ hrad)]

theorem abs_mixedDerivative_le_norm_iteratedFDeriv_on_closedStrip
    {F : PolarPoint → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    {p : PolarPoint} (hp : p.1 ∈ Icc a b) (hFp : ContDiffAt ℝ ∞ F p)
    (i j : ℕ) :
    |mixedDerivative i j F p| ≤ ‖iteratedFDeriv ℝ (i + j) F p‖ := by
  let w : Fin (i + j) → Fin 2 := fun k => if (k : ℕ) < i then 0 else 1
  have hl (k : Fin i) : w (Fin.castAdd j k) = 0 := by
    change (if (k : ℕ) < i then (0 : Fin 2) else 1) = 0
    exact if_pos k.isLt
  have hr (k : Fin j) : w (Fin.natAdd i k) = 1 := by
    change (if i + (k : ℕ) < i then (0 : Fin 2) else 1) = 1
    exact if_neg (by omega)
  have hrad : (∑ k, if w k = 0 then 1 else 0) = i := by
    rw [Fin.sum_univ_add]
    simp [hl, hr]
  have hang : (∑ k, if w k = 0 then 0 else 1) = j := by
    rw [Fin.sum_univ_add]
    simp [hl, hr]
  have he := iteratedFDeriv_cylinderBasis_eq_mixedDerivative_on_closedStrip
    hab hF hp hFp (i + j) w
  rw [hrad, hang] at he
  have hv (k : Fin (i + j)) : ‖cylinderBasisVector (w k)‖ = 1 := by
    unfold cylinderBasisVector
    split <;> norm_num [Prod.norm_mk]
  calc
    |mixedDerivative i j F p| =
        ‖iteratedFDeriv ℝ (i + j) F p (fun k => cylinderBasisVector (w k))‖ := by
      rw [he, Real.norm_eq_abs]
    _ ≤ ‖iteratedFDeriv ℝ (i + j) F p‖ * ∏ k, ‖cylinderBasisVector (w k)‖ :=
      (iteratedFDeriv ℝ (i + j) F p).le_opNorm _
    _ = _ := by simp only [hv, Finset.prod_const_one, mul_one]

end ContinuousFlexibility.Analysis

