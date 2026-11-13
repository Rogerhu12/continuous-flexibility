import ContinuousFlexibility.Analysis.CoupledCircleJointJetAlgebra
import ContinuousFlexibility.Analysis.TameMultilinearNormalization
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# A common low base for genuine joint kernel jets

The existing joint jet differentiates both the chart and the linear source.
Its finite formula contains one base-source term and one term for each
source direction. Common low-base kernel estimates control every term;
multilinear normalization then retains one high factor in the original
product grading. Parameter order is charged only to the high loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFields_boxMajorant
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (low high : Seminorm ℝ E) (m : ℕ) (u : Fin m → E)
    {a R Q : ℝ} (hR : 1 ≤ R) (hQ : 0 ≤ Q) (ha : a ≤ Q)
    (hlow : ∀ i, low (u i) ≤ R) (hhigh : ∀ i, high (u i) ≤ Q) :
    multilinearTameSize low high m a u ≤ ((m : ℝ) + 1) * R ^ m * Q := by
  have hprod (I : Finset (Fin m)) : (∏ i ∈ I, low (u i)) ≤ R ^ m := by
    calc
      _ ≤ ∏ _i ∈ I, R := Finset.prod_le_prod₀
        (fun i _ => apply_nonneg _ _) (fun i _ => hlow i)
      _ = R ^ I.card := by rw [Finset.prod_const]
      _ ≤ R ^ m := pow_le_pow_right₀ hR (by simpa using Finset.card_le_univ I)
  have hmain : a * ∏ i, low (u i) ≤ Q * R ^ m :=
    mul_le_mul ha (hprod Finset.univ) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) hQ
  have hsum : (∑ i, high (u i) * ∏ j ∈ Finset.univ.erase i, low (u j)) ≤
      (m : ℝ) * (Q * R ^ m) := by
    calc
      _ ≤ ∑ _i : Fin m, Q * R ^ m := Finset.sum_le_sum (fun i _ =>
        mul_le_mul (hhigh i) (hprod (Finset.univ.erase i))
          (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) hQ)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (add_le_add hmain hsum).trans_eq (by ring)

private theorem n04PulledFields_seminorm_sum
    {E I : Type*} [AddCommGroup E] [Module ℝ E]
    (q : Seminorm ℝ E) (S : Finset I) (f : I → E) :
    q (∑ i ∈ S, f i) ≤ ∑ i ∈ S, q (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero, le_refl]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add q _ _).trans (add_le_add le_rfl ih)

private theorem n04PulledFields_pair_fst_le
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (s : ℕ) (z : E × E) :
    p s z.1 ≤ pairGrading p p s z := by
  rw [pairGrading_apply]
  exact le_add_of_nonneg_right (apply_nonneg _ _)

private theorem n04PulledFields_pair_snd_le
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (s : ℕ) (z : E × E) :
    p s z.2 ≤ pairGrading p p s z := by
  rw [pairGrading_apply]
  exact le_add_of_nonneg_left (apply_nonneg _ _)

private theorem n04PulledFields_jointJet_bound_of_slots
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
    (K : ∀ r : ℕ, X → X [×(r + 1)]→L[ℝ] Y)
    (low high : Seminorm ℝ X) (q : Seminorm ℝ Y)
    (n : ℕ) (z : X × X) (w : Fin n → X × X) (A R Q : ℝ)
    (hzlow : low z.2 ≤ R) (hzhigh : high z.2 ≤ Q)
    (hwlow : ∀ i, low (w i).1 ≤ R ∧ low (w i).2 ≤ R)
    (hwhigh : ∀ i, high (w i).1 ≤ Q ∧ high (w i).2 ≤ Q)
    (hterm : ∀ r, r ≤ n → ∀ u : Fin (r + 1) → X,
      (∀ i, low (u i) ≤ R) → (∀ i, high (u i) ≤ Q) →
        q (K r z.1 u) ≤ A * Q) :
    q (coupledKernelJointJet K n z w) ≤ ((n : ℝ) + 1) * A * Q := by
  cases n with
  | zero =>
      rw [coupledKernelJointJet_zero_apply]
      have hb := hterm 0 le_rfl (Fin.cons z.2 Fin.elim0)
        (fun i => Fin.cases hzlow (fun j => Fin.elim0 j) i)
        (fun i => Fin.cases hzhigh (fun j => Fin.elim0 j) i)
      simpa only [Nat.cast_zero, zero_add, one_mul] using hb
  | succ n =>
      rw [coupledKernelJointJet_succ_apply]
      have hb := hterm (n + 1) le_rfl (Fin.cons z.2 (fun i => (w i).1))
        (fun i => Fin.cases hzlow (fun j => (hwlow j).1) i)
        (fun i => Fin.cases hzhigh (fun j => (hwhigh j).1) i)
      have hd (i : Fin (n + 1)) := hterm n (Nat.le_succ n)
        (Fin.cons (w i).2 (fun j => (w (i.succAbove j)).1))
        (fun j => Fin.cases (hwlow i).2 (fun k => (hwlow (i.succAbove k)).1) j)
        (fun j => Fin.cases (hwhigh i).2 (fun k => (hwhigh (i.succAbove k)).1) j)
      calc
        _ ≤ q (K (n + 1) z.1 (Fin.cons z.2 (fun i => (w i).1))) +
            ∑ i : Fin (n + 1), q (K n z.1
              (Fin.cons (w i).2 (fun j => (w (i.succAbove j)).1))) :=
          (map_add_le_add q _ _).trans
            (add_le_add le_rfl (n04PulledFields_seminorm_sum q Finset.univ _))
        _ ≤ A * Q + ∑ _i : Fin (n + 1), A * Q :=
          add_le_add hb (Finset.sum_le_sum (fun i _ => hd i))
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

section KernelBounds

variable {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
  (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y) (hp : Monotone p)
  (K : ∀ n : ℕ, X → X [×(n + 1)]→L[ℝ] Y) (base loss : ℕ)
  (hK : ∀ n s R, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, p base x ≤ R → ∀ u : Fin (n + 1) → X,
      q s (K n x u) ≤ C * multilinearTameSize (p base) (p (n + s + loss))
        (n + 1) (1 + p (n + s + loss) x) u)

include hp hK in
private theorem n04PulledFields_kernelJoint_unit_bound (n s : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : X × X, pairGrading p p base z ≤ R →
    ∀ w : Fin n → X × X, (∀ i, pairGrading p p base (w i) < 1) →
      q s (coupledKernelJointJet K n z w) ≤ C *
        ((1 + pairGrading p p (s + (n + loss)) z) +
          ∑ i, pairGrading p p (s + (n + loss)) (w i)) := by
  classical
  let R₀ : ℝ := max R 1
  have hR₀ : 1 ≤ R₀ := le_max_right _ _
  let data := fun j : Fin (n + 1) => hK j.val s R₀ hR₀
  let C : Fin (n + 1) → ℝ := fun j => (data j).choose
  let A : ℝ := ∑ j : Fin (n + 1), C j * (((j.val + 1 : ℕ) : ℝ) + 1) * R₀ ^ (j.val + 1)
  have hC (j : Fin (n + 1)) : 0 ≤ C j := (data j).choose_spec.1
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hC j) (by positivity)) (pow_nonneg (zero_le_one.trans hR₀) _))
  refine ⟨((n : ℝ) + 1) * A, mul_nonneg (by positivity) hA, fun z hz w hw => ?_⟩
  let high : ℕ := s + (n + loss)
  let Q : ℝ := (1 + pairGrading p p high z) + ∑ i, pairGrading p p high (w i)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hsum : 0 ≤ ∑ i, pairGrading p p high (w i) :=
    Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hzQ : 1 + p high z.1 ≤ Q :=
    (add_le_add (le_refl 1) (n04PulledFields_pair_fst_le p high z)).trans
      (le_add_of_nonneg_right hsum)
  have hz₂Q : p high z.2 ≤ Q :=
    (n04PulledFields_pair_snd_le p high z).trans
      ((le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right hsum))
  have hwQ (i : Fin n) : pairGrading p p high (w i) ≤ Q :=
    (Finset.single_le_sum (fun j _ => apply_nonneg (pairGrading p p high) (w j))
      (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left (add_nonneg zero_le_one (apply_nonneg _ _)))
  have hterm (r : ℕ) (hr : r ≤ n) (u : Fin (r + 1) → X)
      (hlow : ∀ i, p base (u i) ≤ R₀) (hhigh : ∀ i, p high (u i) ≤ Q) :
      q s (K r z.1 u) ≤ A * Q := by
    let j : Fin (n + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
    have horder : r + s + loss ≤ high := by dsimp only [high]; omega
    have hm := n04PulledFields_boxMajorant (p base) (p (r + s + loss)) (r + 1) u
      hR₀ hQ ((add_le_add (le_refl 1) (hp horder z.1)).trans hzQ)
      hlow (fun i => (hp horder (u i)).trans (hhigh i))
    have hc : C j * (((r + 1 : ℕ) : ℝ) + 1) * R₀ ^ (r + 1) ≤ A :=
      Finset.single_le_sum
        (f := fun k : Fin (n + 1) =>
          C k * (((k.val + 1 : ℕ) : ℝ) + 1) * R₀ ^ (k.val + 1))
        (fun k _ =>
        mul_nonneg (mul_nonneg (hC k) (by positivity))
          (pow_nonneg (zero_le_one.trans hR₀) _)) (Finset.mem_univ j)
    calc
      _ ≤ C j * multilinearTameSize (p base) (p (r + s + loss))
          (r + 1) (1 + p (r + s + loss) z.1) u :=
        (data j).choose_spec.2 z.1
          (((n04PulledFields_pair_fst_le p base z).trans hz).trans (le_max_left _ _)) u
      _ ≤ C j * ((((r + 1 : ℕ) : ℝ) + 1) * R₀ ^ (r + 1) * Q) :=
        mul_le_mul_of_nonneg_left hm (hC j)
      _ = (C j * (((r + 1 : ℕ) : ℝ) + 1) * R₀ ^ (r + 1)) * Q := by ring
      _ ≤ A * Q := mul_le_mul_of_nonneg_right hc hQ
  exact n04PulledFields_jointJet_bound_of_slots K (p base) (p high) (q s) n z w A R₀ Q
    (((n04PulledFields_pair_snd_le p base z).trans hz).trans (le_max_left _ _)) hz₂Q
    (fun i => ⟨((n04PulledFields_pair_fst_le p base (w i)).trans (hw i).le).trans hR₀,
      ((n04PulledFields_pair_snd_le p base (w i)).trans (hw i).le).trans hR₀⟩)
    (fun i => ⟨(n04PulledFields_pair_fst_le p high (w i)).trans (hwQ i),
      (n04PulledFields_pair_snd_le p high (w i)).trans (hwQ i)⟩) hterm

include hp hK in
/-- The low base is unchanged at every joint parameter order. The high
loss is `n + loss`, fixed before the spatial order and low-box radius. -/
theorem n04PulledFields_coupledKernelJointJet_fixedBase :
    ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : X × X, pairGrading p p base z ≤ R → ∀ w : Fin n → X × X,
        q s (coupledKernelJointJet K n z w) ≤
          C * tameJetSize (pairGrading p p) n s (n + loss) base z w := by
  intro n R hR s
  let data := n04PulledFields_kernelJoint_unit_bound p q hp K base loss hK n s R hR
  refine ⟨data.choose, data.choose_spec.1, fun z hz w => ?_⟩
  exact multilinear_bound_of_unitBall (coupledKernelJointJet K n z) (q s)
    (pairGrading p p base) (pairGrading p p (s + (n + loss))) data.choose_spec.1
    (data.choose_spec.2 z hz) w

end KernelBounds

end ContinuousFlexibility.Analysis
