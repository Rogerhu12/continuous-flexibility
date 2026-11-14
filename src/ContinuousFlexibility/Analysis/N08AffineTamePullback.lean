module

public import ContinuousFlexibility.Analysis.SolveNewtonBridge
public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Pulling genuine tame towers back to an affine sector chart

Translation changes only the constants in the one-high estimate. A bounded
linear inclusion then retains the existing input grading and derivative
loss. The target can be any topological real module, including the actual
compatible source subspace.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section Translation

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [IsTopologicalAddGroup X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  {U : Set X} {f : X → Y}

def n08SmoothDirectionsTranslate (J : SmoothDirections U f) (a : X) :
    SmoothDirections ((fun x => a + x) ⁻¹' U) (fun x => f (a + x)) where
  open_domain := J.open_domain.preimage (continuous_const.add continuous_id)
  D := fun n x => J.D n (a + x)
  zero := fun x hx => J.zero (a + x) hx
  continuous := fun n => (J.continuous n).comp
    ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
    (fun z hz => ⟨hz.1, mem_univ _⟩)
  derivative := fun n x hx v w => by
    have h := J.derivative n (a + x) hx v w
    simpa only [HasProjectiveLineDerivAt, add_assoc] using h

theorem n08_tameJetSize_translate (p : ℕ → Seminorm ℝ X) (k s loss base : ℕ)
    (a x : X) (v : Fin k → X) :
    tameJetSize p k s loss base (a + x) v ≤
      (1 + p (s + loss) a) * tameJetSize p k s loss base x v := by
  have hfirst : 1 + p (s + loss) (a + x) ≤
      (1 + p (s + loss) a) * (1 + p (s + loss) x) := by
    have h := map_add_le_add (p (s + loss)) a x
    nlinarith only [h, mul_nonneg (apply_nonneg (p (s + loss)) a)
      (apply_nonneg (p (s + loss)) x)]
  have hprod : 0 ≤ ∏ i, p base (v i) :=
    Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)
  have hsum : 0 ≤ ∑ i : Fin k, p (s + loss) (v i) *
      ∏ j ∈ Finset.univ.erase i, p base (v j) := by positivity
  have hsum' := le_mul_of_one_le_left hsum
    (le_add_of_nonneg_right (apply_nonneg (p (s + loss)) a))
  unfold tameJetSize
  exact (add_le_add (mul_le_mul_of_nonneg_right hfirst hprod) hsum').trans_eq (by ring)

theorem n08_smoothTameOn_translate
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    (h : SmoothTameOn p q U f) (a : X) :
    SmoothTameOn p q ((fun x => a + x) ⁻¹' U) (fun x => f (a + x)) := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨n08SmoothDirectionsTranslate J a, fun k x0 hx0 => ?_⟩
  obtain ⟨loss, base, ε, hε, hb⟩ := hJ k (a + x0) hx0
  refine ⟨loss, base, ε, hε, fun s hs => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hb s hs
  refine ⟨C * (1 + p (s + loss) a),
    mul_nonneg hC (add_nonneg zero_le_one (apply_nonneg _ _)), ?_⟩
  intro x hx hnear v
  have hnear' : p base ((a + x) - (a + x0)) < ε := by
    simpa only [add_sub_add_left_eq_sub] using hnear
  change q s (J.D k (a + x) v) ≤
    (C * (1 + p (s + loss) a)) * tameJetSize p k s loss base x v
  exact (hCb (a + x) hx hnear' v).trans
    ((mul_le_mul_of_nonneg_left
      (n08_tameJetSize_translate p k s loss base a x v) hC).trans_eq (by ring))

end Translation

section Affine

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
  {U : Set Y} {f : Y → Z}

theorem n08_smoothTameOn_affine_pullback
    (h : SmoothTameOn q r U f) (a : Y) (L : X →L[ℝ] Y)
    {A : ℝ} (hA : 1 ≤ A) (hL : ∀ n x, q n (L x) ≤ A * p n x) :
    SmoothTameOn p r {x | a + L x ∈ U} (fun x => f (a + L x)) :=
  solve_smoothTameOn_precomp (n08_smoothTameOn_translate h a) L hA hL

end Affine

end ContinuousFlexibility.Analysis
