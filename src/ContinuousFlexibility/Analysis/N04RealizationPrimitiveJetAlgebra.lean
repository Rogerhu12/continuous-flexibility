import ContinuousFlexibility.Analysis.N04RealizationEnvelopeJacobian
import ContinuousFlexibility.Analysis.N01cOuterDenominatorJets
import ContinuousFlexibility.Radial.ReferenceColumnSmooth

/-!
# Finite jet algebra for the actual primitive factors

Positive coordinate compositions require no zeroth coordinate bound.
The derivative application uses the genuine continuous linear map and
one arbitrary vector field. The three fixed reference profile columns
have uniform jets on the closed physical radial interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff BigOperators

section JetAlgebra

variable {X V E F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Neither coordinate map needs its unwrapped angular value bounded. -/
theorem n04Realization_envelope_comp_positive_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → V)
    (f : X → E → F) (g : X → V → E)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (g x (p x)))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x)) {n : ℕ} (hn : 0 < n)
    (hfj : ∀ j, 0 < j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (g x (p x))‖))
    (hgj : ∀ j, 0 < j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (g x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (f x ∘ g x) (p x)‖) := by
  classical
  have hsum := hasPositiveEnvelope_finsetSum hW (Finset.univ : Finset (OrderedFinpartition n))
    (fun c x => ‖iteratedFDeriv ℝ c.length (f x) (g x (p x))‖ *
      ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) (g x) (p x)‖) (by
      intro c _
      have hprod := hasPositiveEnvelope_finsetProd hW (Finset.univ : Finset (Fin c.length))
        (fun j x => ‖iteratedFDeriv ℝ (c.partSize j) (g x) (p x)‖)
        (fun _ _ _ => norm_nonneg _)
        (fun j _ => hgj _ (c.partSize_pos j) (c.partSize_le j))
      exact (hfj c.length (c.length_pos hn) c.length_le).mul hW hprod
        (fun x => Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact hsum.mono (fun x => norm_iteratedFDeriv_comp_le_partition_sum (hf x) (hg x) n)

/-- A vector fixed in the spatial variable retains its value envelope. -/
theorem n04Realization_envelope_const_jets
    {W : X → ℝ} (p : X → V) (c : X → E)
    (hc : HasPositiveEnvelope W (fun x => ‖c x‖)) (n : ℕ) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fun _ : V => c x) (p x)‖) := by
  apply hc.mono
  intro x
  cases n with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ n =>
      simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using norm_nonneg (c x)

/-- The same derivative application treats the current inverse-angular
column and each transported reference column. -/
theorem n04Realization_envelope_derivative_apply_comp_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → V)
    (f : X → E → F) (q : X → V → E) (v : X → V → E)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (q x (p x)))
    (hq : ∀ x, ContDiffAt ℝ ∞ (q x) (p x))
    (hv : ∀ x, ContDiffAt ℝ ∞ (v x) (p x)) (n : ℕ)
    (hfj : ∀ j, 0 < j → j ≤ n + 1 → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (q x (p x))‖))
    (hqj : ∀ j, 0 < j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (q x) (p x)‖))
    (hvj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (v x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n
        (fun y => fderiv ℝ (f x) (q x y) (v x y)) (p x)‖) := by
  have hd (x : X) : ContDiffAt ℝ ∞
      (fun y => fderiv ℝ (f x) (q x y)) (p x) :=
    ((hf x).fderiv_right (m := ∞) (by simp)).comp (p x) (hq x)
  have hdj (j : ℕ) (hj : j ≤ n) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (fun y => fderiv ℝ (f x) (q x y)) (p x)‖) := by
    exact n04Realization_envelope_comp_jets hW p
      (fun x => fderiv ℝ (f x)) q
      (fun x => (hf x).fderiv_right (m := ∞) (by simp)) hq j
      (fun k hk => n04Realization_envelope_fderiv_jets (fun x => q x (p x)) f k
        (hfj (k + 1) (by omega) (by omega)))
      (fun k hk hkj => hqj k hk (hkj.trans hj))
  exact n04Realization_envelope_clm_apply_jets hW p
    (fun x y => fderiv ℝ (f x) (q x y)) v hd hv n hdj hvj

end JetAlgebra

section ProfileColumns

variable {D : ReferenceData}

/-- These are exactly the three profile columns in the stored primitive
field, including the globally smooth flat quotient. -/
theorem n04Realization_referenceProfile_contDiff
    (ha : 0 < D.a) (hw : EndpointFlat D D.w) (i : Fin 3) :
    ContDiff ℝ ∞ (fun r : ℝ =>
      if i = 0 then deriv D.w r else if i = 1 then D.w r else deriv D.w r / r) := by
  split_ifs
  · exact (contDiff_infty_iff_deriv.mp hw.1).2
  · exact hw.1
  · exact reference_contDiff_flat_deriv_div ha hw

theorem n04Realization_referenceProfile_finite_jets
    (ha : 0 < D.a) (hw : EndpointFlat D D.w) (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ i : Fin 3, ∀ n : ℕ, n ≤ N →
      ∀ r ∈ Icc D.a D.b,
        ‖iteratedFDeriv ℝ n (fun t : ℝ =>
          if i = 0 then deriv D.w t else if i = 1 then D.w t else deriv D.w t / t) r‖ ≤ B := by
  classical
  have hbound (i : Fin 3) : ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, n ≤ N →
      ∀ r ∈ Icc D.a D.b,
        ‖iteratedFDeriv ℝ n (fun t : ℝ =>
          if i = 0 then deriv D.w t else if i = 1 then D.w t else deriv D.w t / t) r‖ ≤ B :=
    compact_iteratedFDeriv_bound isCompact_Icc
      (fun _ _ => (n04Realization_referenceProfile_contDiff ha hw i).contDiffAt) N
  choose B hB hb using hbound
  have hsum : 0 ≤ ∑ i : Fin 3, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨1 + ∑ i : Fin 3, B i, add_pos_of_pos_of_nonneg zero_lt_one hsum,
    fun i n hn r hr => (hb i n hn r hr).trans ?_⟩
  exact (Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem n04Realization_referenceProfile_envelope
    {X : Type*} (ha : 0 < D.a) (hw : EndpointFlat D D.w)
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → ℝ)
    (hp : ∀ x, p x ∈ Icc D.a D.b) (i : X → Fin 3) (n : ℕ) :
    HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n
      (fun t : ℝ => if i x = 0 then deriv D.w t
        else if i x = 1 then D.w t else deriv D.w t / t) (p x)‖) := by
  obtain ⟨B, _, hb⟩ := n04Realization_referenceProfile_finite_jets ha hw n
  exact (hasPositiveEnvelope_const W hW B).mono
    (fun x => hb (i x) n le_rfl (p x) (hp x))

end ProfileColumns

end ContinuousFlexibility.Analysis
