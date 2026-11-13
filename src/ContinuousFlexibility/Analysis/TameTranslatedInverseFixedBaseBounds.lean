import ContinuousFlexibility.Analysis.TameInverseFixedBaseBounds
import ContinuousFlexibility.Analysis.SolveNewtonBridge

/-!
# Fixed-base bounds for translated instances of one inverse family

The common domain, the two original inverse identities, and the forward
and value estimates are supplied on abstract data. All choices of bases,
losses and constants precede the concrete realization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E Travel : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

theorem translatedInverseFamily_fixedBase_oneHigh
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (hinterp : HasInterpolation (pairGrading p p))
    (F : Travel → E → E →L[ℝ] E) (Q : Travel → E → E →ₗ[ℝ] E)
    (zero : Travel) (W U : Set E) (hU : IsOpen U) (hsub : U ⊆ W)
    (allowed : Travel → E → Prop)
    (hallowed : ∀ travel e, allowed travel e → e ∈ U)
    (JF : SmoothDirections univ (fun z : E × E => F zero z.1 z.2))
    (JP₀ : SmoothDirections (W ×ˢ univ) (fun z : E × E => Q zero z.1 z.2))
    (translate : Travel → E →L[ℝ] E)
    (htranslate : ∀ travel e, e ∈ U → ∀ y,
      Q travel e y = translate travel (Q zero e y))
    (htranslateBound : ∀ travel s y, p s (translate travel y) ≤ p s y)
    (hleftInverse : ∀ e ∈ U, ∀ y, Q zero e (F zero e y) = y)
    (hrightInverse : ∀ e ∈ U, ∀ y, F zero e (Q zero e y) = y)
    (hvalue : ∃ bv lv : ℕ, ∀ R : ℝ, 1 ≤ R → ∀ s,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ e ∈ U, p bv e ≤ R → ∀ y,
        p s (Q zero e y) ≤ C * ((1 + p (s + lv) e) * p bv y + p (s + lv) y))
    (hforward : ∃ bf lf : ℕ, ∀ n (R : ℝ), 1 ≤ R → ∀ s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (travel : Travel) (V : Set E) (hV : IsOpen V)
          (J : SmoothDirections (V ×ˢ univ) (fun z : E × E => F travel z.1 z.2)),
          ∀ e ∈ V, p bf e ≤ R → ∀ v : Fin n → E,
            (∀ i, p bf (v i) ≤ R) → ∀ y,
              p s (inverseForwardJet J n e v y) ≤ C *
                ((1 + p (s + (n + lf)) e + ∑ i, p (s + (n + lf)) (v i)) *
                  p bf y + p (s + (n + lf)) y)) :
    ∃ base : ℕ, ∀ n : ℕ, ∃ loss : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (travel : Travel)
        (JP : SmoothDirections (W ×ˢ univ) (fun z : E × E => Q travel z.1 z.2)),
        ∀ x : E × E, allowed travel x.1 →
          pairGrading p p base x ≤ R → ∀ v : Fin n → E × E,
            p s (JP.D n x v) ≤ C * tameJetSize (pairGrading p p) n s loss base x v := by
  classical
  obtain ⟨bv, lv, hv⟩ := hvalue
  obtain ⟨bf, lf, hf⟩ := hforward
  let b : ℕ := max bv bf
  have hq : Monotone p := hp
  let L : E → E →L[ℝ] E := F zero
  let P : E → E →ₗ[ℝ] E := Q zero
  let J : SmoothDirections (U ×ˢ univ) (fun z : E × E => L z.1 z.2) :=
    JF.restrict (hU.prod isOpen_univ) (subset_univ _)
  have hcont : ContinuousOn (fun z : E × E => P z.1 z.2) (U ×ˢ univ) :=
    JP₀.continuousOn.mono (fun x hx => ⟨hsub hx.1, hx.2⟩)
  let V : E → E →L[ℝ] E := inverseFamilyContinuousLinearMap P hcont
  have hV (e : E) (he : e ∈ U) (y : E) : V e y = P e y :=
    inverseFamilyContinuousLinearMap_apply P hcont he y
  have hVc : ContinuousOn (fun z : E × E => V z.1 z.2) (U ×ˢ univ) :=
    continuousOn_inverseFamilyContinuousLinearMap P hcont
  have hleft (e : E) (he : e ∈ U) (y : E) : V e (L e y) = y :=
    (hV e he (L e y)).trans (hleftInverse e he y)
  have hright (e : E) (he : e ∈ U) (y : E) : L e (V e y) = y :=
    (congrArg (L e) (hV e he y)).trans (hrightInverse e he y)
  have hVB : ∀ R : ℝ, 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ e ∈ U, p b e ≤ R → ∀ y : E,
        p s (V e y) ≤ C *
          ((1 + p (s + lv) e) * p b y + p (s + lv) y) := by
    intro R hR s
    obtain ⟨C, hC, hb⟩ := hv R hR s
    refine ⟨C, hC, fun e he heR y => ?_⟩
    rw [hV e he y]
    exact (hb e he ((hq (le_max_left _ _) e).trans heR) y).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (hq (le_max_left _ _) y)
          (add_nonneg zero_le_one (apply_nonneg _ _))) le_rfl) hC)
  have hFB : ∀ n (R : ℝ), 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ e ∈ U, p b e ≤ R → ∀ v : Fin n → E,
        (∀ i, p b (v i) ≤ R) → ∀ y : E,
        p s (inverseForwardJet J n e v y) ≤ C *
          ((1 + p (s + (n + lf)) e + ∑ i, p (s + (n + lf)) (v i)) *
            p b y + p (s + (n + lf)) y) := by
    intro n R hR s
    obtain ⟨C, hC, hb⟩ := hf n R hR s
    refine ⟨C, hC, fun e he heR v hv y => ?_⟩
    have h := hb zero U hU J e he
      ((hq (le_max_right _ _) e).trans heR) v
      (fun i => (hq (le_max_right _ _) (v i)).trans (hv i)) y
    have hz : 0 ≤ 1 + p (s + (n + lf)) e +
        ∑ i, p (s + (n + lf)) (v i) :=
      add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
        (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (hq (le_max_right _ _) y) hz) le_rfl) hC)
  let JV := inverseFamilySmoothDirections J hU V hleft hright hVc
  let Jactual : SmoothDirections (U ×ˢ univ) (fun z : E × E => P z.1 z.2) :=
    JV.congr (fun x hx => hV x.1 hx.1 x.2)
  obtain ⟨base, hbase⟩ := inverseFamilySmoothDirections_fixedBase_oneHigh
    p hq J V b lv lf hVB hFB
    hinterp hU hleft hright hVc
  refine ⟨base, fun n => ?_⟩
  obtain ⟨loss, hloss⟩ := hbase n
  refine ⟨loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hb⟩ := hloss R hR s
  refine ⟨C, hC, fun travel JP x hx hxR v => ?_⟩
  have hxU : x ∈ U ×ˢ univ := ⟨hallowed travel x.1 hx, mem_univ _⟩
  let τ : E →L[ℝ] E := translate travel
  let JT : SmoothDirections (U ×ˢ univ) (fun z : E × E =>
      Q travel z.1 z.2) :=
    (solveSmoothDirectionsPostcomp Jactual τ).congr (fun z hz =>
      (htranslate travel z.1 hz.1 z.2).symm)
  have hjet := HasProjectiveJetsOn.unique (hU.prod isOpen_univ)
    (JP.restrict (hU.prod isOpen_univ)
      (fun z hz => ⟨hsub hz.1, hz.2⟩)).hasProjectiveJetsOn JT.hasProjectiveJetsOn n x hxU
  have hvalue : JP.D n x v = τ (JV.D n x v) := by
    simpa only [JT, SmoothDirections.congr, solveSmoothDirectionsPostcomp,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, Jactual] using
      congrArg (fun A : (E × E) [×n]→L[ℝ] E => A v) hjet
  rw [hvalue]
  exact (htranslateBound travel s (JV.D n x v)).trans (hb x hxU hxR v)

end ContinuousFlexibility.Analysis
