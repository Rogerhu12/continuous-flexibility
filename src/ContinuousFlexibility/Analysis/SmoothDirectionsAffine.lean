import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.ProjectiveJets

/-!
# Affine restriction and uniqueness of directional towers

The sector parameters enter the physical state by a fixed translation
and a continuous linear inclusion. This operation retains the actual
multilinear jets and their difference-quotient identities.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

section Affine

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  {U : Set F} {V : Set E} {f : F → G}

def SmoothDirections.congrOn (J : SmoothDirections U f) {g : F → G}
    (hfg : EqOn f g U) : SmoothDirections U g where
  open_domain := J.open_domain
  D := J.D
  zero x hx := (J.zero x hx).trans (hfg hx)
  continuous := J.continuous
  derivative := J.derivative

def SmoothDirections.compAffine (J : SmoothDirections U f)
    (L : E →L[ℝ] F) (a : F) (hV : IsOpen V)
    (hmap : MapsTo (fun x => a + L x) V U) :
    SmoothDirections V (fun x => f (a + L x)) where
  open_domain := hV
  D n x := (J.D n (a + L x)).compContinuousLinearMap (fun _ => L)
  zero x hx := by
    change J.D 0 (a + L x) (fun i : Fin 0 => L (Fin.elim0 i)) = f (a + L x)
    have he : (fun i : Fin 0 => L (Fin.elim0 i)) = Fin.elim0 := Subsingleton.elim _ _
    rw [he]
    exact J.zero _ (hmap hx)
  continuous n := by
    have hc : Continuous (fun z : E × (Fin n → E) =>
        (a + L z.1, fun i => L (z.2 i))) :=
      (continuous_const.add (L.continuous.comp continuous_fst)).prodMk
        (continuous_pi (fun i => L.continuous.comp ((continuous_apply i).comp continuous_snd)))
    exact (J.continuous n).comp hc.continuousOn (fun z hz => ⟨hmap hz.1, mem_univ _⟩)
  derivative n x hx v w := by
    have hd := J.derivative n (a + L x) (hmap hx) (fun i => L (v i)) (L w)
    have he : (fun i : Fin (n + 1) => L ((Fin.cons w v : Fin (n + 1) → E) i)) =
        Fin.cons (L w) (fun i => L (v i)) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp only [Fin.cons_zero, Fin.cons_succ]
    unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt at hd ⊢
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, he,
      map_add, map_smul, ← add_assoc]
    exact hd

theorem SmoothDirections.compAffine_apply (J : SmoothDirections U f)
    (L : E →L[ℝ] F) (a : F) (hV : IsOpen V)
    (hmap : MapsTo (fun x => a + L x) V U)
    (n : ℕ) (x : E) (v : Fin n → E) :
    (J.compAffine L a hV hmap).D n x v = J.D n (a + L x) (fun i => L (v i)) := rfl

end Affine

section Unique

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
  {U : Set E} {f : E → F}

theorem SmoothDirections.unique (J K : SmoothDirections U f) :
    ∀ n x, x ∈ U → J.D n x = K.D n x :=
  HasProjectiveJetsOn.unique J.open_domain
    ⟨J.zero, J.continuous, fun n x hx w v => J.derivative n x hx v w⟩
    ⟨K.zero, K.continuous, fun n x hx w v => K.derivative n x hx v w⟩

end Unique

section Bounds

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A one-high-factor estimate also gives a product estimate in one
fixed seminorm. This estimate is used only for existence and continuity
of jets; the sharper original estimate is retained for tame bounds. -/
theorem oneHighVariationWeight_le_seminorm_product
    (p : ℕ → Seminorm ℝ E) (q : Seminorm ℝ E) (base high : ℕ)
    (hbase : p base ≤ q) (hhigh : p high ≤ q) {k : ℕ}
    (x : E) (v : Fin k → E) :
    oneHighVariationWeight p base high x v ≤
      ((k : ℝ) + 1) * (1 + q x) * ∏ i, q (v i) := by
  classical
  have hprod (s : Finset (Fin k)) : (∏ i ∈ s, p base (v i)) ≤ ∏ i ∈ s, q (v i) :=
    Finset.prod_le_prod₀ (fun i hi => apply_nonneg _ _) (fun i hi => hbase (v i))
  have hterm (i : Fin k) :
      p high (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j) ≤ ∏ j, q (v j) := by
    calc
      _ ≤ q (v i) * ∏ j ∈ Finset.univ.erase i, q (v j) :=
        mul_le_mul (hhigh (v i)) (hprod _) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
          (apply_nonneg _ _)
      _ = _ := Finset.mul_prod_erase Finset.univ (fun j => q (v j)) (Finset.mem_univ i)
  have hsum : (∑ i : Fin k, p high (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j)) ≤
      (k : ℝ) * ∏ j, q (v j) := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hterm i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
  have hp0 : 0 ≤ ∏ i, q (v i) := Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)
  unfold oneHighVariationWeight
  have hfirst := mul_le_mul (add_le_add_right (hhigh x) 1) (hprod Finset.univ)
    (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (add_nonneg zero_le_one (apply_nonneg _ _))
  have hraw := add_le_add hfirst hsum
  have hextra : 0 ≤ (k : ℝ) * q x * ∏ i, q (v i) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (apply_nonneg _ _)) hp0
  nlinarith only [hraw, hextra]

end Bounds

end ContinuousFlexibility.Statements
