import ContinuousFlexibility.Analysis.SpacesInterpolationProducts
import ContinuousFlexibility.Analysis.TameTopologicalComposition
import ContinuousFlexibility.Analysis.TameMultilinearNormalization
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Ordered-partition composition with one fixed low base

The public finite-product interpolation theorem is applied to the original
inputs. Parameter-order losses are assigned differential orders in that
product. They never become additional low-neighborhood hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

/-- The base and loss precede both finite arities and every assigned order. -/
theorem spaces_interpolation_affine_product_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (hI : HasInterpolation (pairGrading realGrading p)) :
    ∃ B L : ℕ, ∀ k m : ℕ, ∀ order : Fin m → ℕ, ∀ s : ℕ,
      (∑ j, order j) ≤ s → ∀ R : ℝ, 0 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin (k + 1) → E,
        (∀ i, p B (x i) ≤ R) →
        (∏ j, (1 + ∑ i, p (order j) (x i))) ≤
          C * (1 + ∑ i, p (s + L) (x i)) := by
  letI : TopologicalSpace E := ⊥
  classical
  let q := pairGrading realGrading p
  have hq : Monotone q := tamePairGrading_monotone (fun _ _ _ _ => le_rfl) hp
  have hqone (t : ℕ) (x : E) : q t (1, x) = 1 + p t x := by
    simp only [q, pairGrading_apply, realGrading, coe_normSeminorm, norm_one]
  obtain ⟨B, L, hprod⟩ := spaces_interpolation_product_bound q (fun x _ _ h => hq h x) hI
  refine ⟨B, L, fun k m order s hs R hR => ?_⟩
  cases m with
  | zero =>
      refine ⟨1, zero_le_one, fun x _ => ?_⟩
      simp only [Fin.prod_univ_zero, one_mul]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  | succ m =>
      obtain ⟨A, hA, ha⟩ := hprod order s hs
      let M : ℝ := (k + 1 : ℕ)
      refine ⟨M ^ (m + 1) * A * (m + 1 : ℕ) * (1 + R) ^ (m + 1),
        by dsimp [M]; positivity, fun x hx => ?_⟩
      have hmax (j : Fin (m + 1)) : ∃ i : Fin (k + 1),
          ∀ l : Fin (k + 1), q (order j) (1, x l) ≤ q (order j) (1, x i) := by
        obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image
          (fun l : Fin (k + 1) => q (order j) (1, x l)) Finset.univ_nonempty
        exact ⟨i, fun l => hi l (Finset.mem_univ l)⟩
      choose pick hpick using hmax
      let P : ℝ := 1 + ∑ i, p (s + L) (x i)
      have hP : 0 ≤ P := by dsimp [P]; positivity
      have hfactor (j : Fin (m + 1)) :
          1 + ∑ i, p (order j) (x i) ≤ M * q (order j + 2) (1, x (pick j)) := by
        calc
          _ ≤ ∑ i : Fin (k + 1), q (order j) (1, x i) := by
            simp only [hqone, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
            have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
            exact add_le_add hk le_rfl
          _ ≤ ∑ _i : Fin (k + 1), q (order j + 2) (1, x (pick j)) :=
            Finset.sum_le_sum (fun i _ => (hpick j i).trans (hq (by omega) _))
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, M]
      have hlow (j : Fin (m + 1)) : q B (1, x (pick j)) ≤ 1 + R := by
        rw [hqone]; exact add_le_add le_rfl (hx (pick j))
      have hhigh (j : Fin (m + 1)) : q (s + L) (1, x (pick j)) ≤ P := by
        rw [hqone]
        exact add_le_add le_rfl (Finset.single_le_sum
          (fun (i : Fin (k + 1)) _ => apply_nonneg (p (s + L)) (x i))
          (Finset.mem_univ (pick j)))
      have herase (j : Fin (m + 1)) :
          (∏ l ∈ Finset.univ.erase j, q B (1, x (pick l))) ≤ (1 + R) ^ (m + 1) := by
        calc
          _ ≤ ∏ _l ∈ Finset.univ.erase j, (1 + R) :=
            Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun l _ => hlow l)
          _ ≤ ∏ _l : Fin (m + 1), (1 + R) :=
            Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.erase_subset _ _)
              (fun _ _ => by positivity) (fun _ _ _ => by linarith)
          _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hsum : (∑ j, q (s + L) (1, x (pick j)) *
          ∏ l ∈ Finset.univ.erase j, q B (1, x (pick l))) ≤
          (m + 1 : ℕ) * (P * (1 + R) ^ (m + 1)) := by
        calc
          _ ≤ ∑ _j : Fin (m + 1), P * (1 + R) ^ (m + 1) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul (hhigh j) (herase j)
              (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) hP)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      calc
        _ ≤ ∏ j, M * q (order j + 2) (1, x (pick j)) :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hfactor j)
        _ = M ^ (m + 1) * ∏ j, q (order j + 2) (1, x (pick j)) := by
          rw [Finset.prod_mul_distrib]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ M ^ (m + 1) * (A * ((m + 1 : ℕ) * (P * (1 + R) ^ (m + 1)))) :=
          mul_le_mul_of_nonneg_left ((ha (fun j => (1, x (pick j)))).trans
            (mul_le_mul_of_nonneg_left hsum hA)) (by dsimp [M]; positivity)
        _ = _ := by dsimp only [P]; ring

private theorem tameJetSize_selected_unit_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B t L n m : ℕ) (x : E) (v : Fin n → E)
    (σ : Fin m → Fin n) (hv : ∀ i, p B (v i) ≤ 1) :
    tameJetSize p m t L B x (v ∘ σ) ≤
      (m + 1 : ℕ) * (1 + ∑ i, p (t + L) ((Fin.cons x v : Fin (n + 1) → E) i)) := by
  letI : TopologicalSpace E := ⊥
  let P : ℝ := 1 + ∑ i, p (t + L) ((Fin.cons x v : Fin (n + 1) → E) i)
  have hslot (i : Fin (n + 1)) : p (t + L) ((Fin.cons x v : Fin (n + 1) → E) i) ≤ P :=
    (Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hx : 1 + p (t + L) x ≤ P := by
    dsimp [P]
    rw [Fin.sum_univ_succ]
    exact add_le_add le_rfl (le_add_of_nonneg_right
      (Finset.sum_nonneg (fun (i : Fin n) _ => apply_nonneg (p (t + L)) (v i))))
  have hs : (∑ j, p (t + L) (v (σ j))) ≤ (m : ℝ) * P := by
    calc
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hslot (Fin.succ (σ j)))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  exact (multilinearTameSize_le_affine (p B) (p (t + L)) m
    (by positivity) (v ∘ σ) (fun i => hv (σ i))).trans
      ((add_le_add hx hs).trans_eq (by dsimp only [P]; push_cast; ring))

private theorem tameJetSize_uniform_slots
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (q : ℕ → Seminorm ℝ F) (n s L B : ℕ) (x : F) (v : Fin n → F)
    (A H : ℝ) (hA : 1 ≤ A) (hH : 1 ≤ H)
    (hx : q (s + L) x ≤ H) (hv : ∀ i, q (s + L) (v i) ≤ H)
    (hlow : ∀ i, q B (v i) ≤ A) :
    tameJetSize q n s L B x v ≤ ((n : ℝ) + 2) * H * A ^ n := by
  have hp (S : Finset (Fin n)) : (∏ i ∈ S, q B (v i)) ≤ A ^ n := by
    calc
      _ ≤ ∏ _i ∈ S, A := Finset.prod_le_prod₀
        (fun _ _ => apply_nonneg _ _) (fun i _ => hlow i)
      _ ≤ ∏ _i : Fin n, A := Finset.prod_le_prod_of_subset_of_one_le₀
        (Finset.subset_univ _) (fun _ _ => zero_le_one.trans hA) (fun _ _ _ => hA)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbase : 1 + q (s + L) x ≤ 2 * H := by linarith
  have hsum : (∑ i, q (s + L) (v i) * ∏ j ∈ Finset.univ.erase i, q B (v j)) ≤
      (n : ℝ) * (H * A ^ n) := by
    calc
      _ ≤ ∑ _i : Fin n, H * A ^ n := Finset.sum_le_sum (fun i _ =>
        mul_le_mul (hv i) (hp _) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
          (zero_le_one.trans hH))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  exact (add_le_add (mul_le_mul hbase (hp _)
    (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (by linarith)) hsum).trans_eq (by ring)


/-- Every partition is estimated from its actual inner and outer towers.
The single input base is chosen before all parameter orders. -/
theorem projectiveCompositionJets_fixedBase_oneHigh
    {I E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G] [IsTopologicalAddGroup G]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (r : ℕ → Seminorm ℝ G)
    (hp : Monotone p) (hI : HasInterpolation (pairGrading realGrading p))
    {U : Set E} {V : Set F} {f : I → E → F} {g : I → F → G}
    (J : ∀ i, SmoothDirections U (f i)) (K : ∀ i, SmoothDirections V (g i))
    (BJ BK : ℕ) (d e : ℕ → ℕ)
    (hJ : ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, x ∈ U → p BJ x ≤ R → ∀ v : Fin n → E,
        q s ((J i).D n x v) ≤ C * tameJetSize p n s (d n) BJ x v)
    (hK : ∀ n R, 0 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i y, y ∈ V → q BK y ≤ R → ∀ v : Fin n → F,
        r s ((K i).D n y v) ≤ C * tameJetSize q n s (e n) BK y v)
    (hmap : ∀ i, MapsTo (f i) U V) :
    ∃ B : ℕ, BJ ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → p B x ≤ R →
      ∀ v : Fin n → E,
        r s (projectiveCompositionJets (f i) (J i).D (K i).D n x v) ≤
          C * tameJetSize p n s L B x v := by
  classical
  obtain ⟨BP, LP, hproduct⟩ := spaces_interpolation_affine_product_bound p hp hI
  let B : ℕ := max BJ (max BP (BK + d 0))
  have hBJ : BJ ≤ B := le_max_left _ _
  have hBP : BP ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBK : BK + d 0 ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hBJ, fun n => ?_⟩
  let δ : ℕ := ∑ j : Fin (n + 1), d j.val
  have hd (j : ℕ) (hj : j ≤ n) : d j ≤ δ := by
    dsimp only [δ]
    exact Finset.single_le_sum (fun (l : Fin (n + 1)) _ => Nat.zero_le (d l.val))
      (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (n + 1)))
  let termLoss (c : OrderedFinpartition n) : ℕ :=
    e c.length + δ + c.length * (BK + δ) + LP
  let L : ℕ := Finset.univ.sup termLoss
  have hL (c : OrderedFinpartition n) : termLoss c ≤ L :=
    Finset.le_sup (Finset.mem_univ c)
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨C₀, hC₀, hc₀⟩ := hJ 0 R hR BK
  let R₀ : ℝ := C₀ * (1 + R)
  have hR₀ : 0 ≤ R₀ := mul_nonneg hC₀ (add_nonneg zero_le_one hR)
  have hlowImage (i : I) (x : E) (hx : x ∈ U) (hbx : p B x ≤ R) :
      q BK (f i x) ≤ R₀ := by
    have hb := hc₀ i x hx ((hp hBJ x).trans hbx) Fin.elim0
    rw [(J i).zero x hx, tameJetSize_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((hp hBK x).trans hbx)) hC₀)
  have hinner (t : ℕ) : ∃ A : ℝ, 1 ≤ A ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ v : Fin n → E,
      (∀ l, p B (v l) ≤ 1) → ∀ j : ℕ, j ≤ n → ∀ σ : Fin j → Fin n,
      q t ((J i).D j x (v ∘ σ)) ≤
        A * (1 + ∑ l, p (t + δ) ((Fin.cons x v : Fin (n + 1) → E) l)) := by
    choose C hC hc using fun j : Fin (n + 1) => hJ j.val R hR t
    let A : ℝ := 1 + ∑ j : Fin (n + 1), C j * (j.val + 1 : ℕ)
    have hA : 1 ≤ A := le_add_of_nonneg_right
      (Finset.sum_nonneg (fun j _ => mul_nonneg (hC j) (Nat.cast_nonneg _)))
    refine ⟨A, hA, fun i x hx hbx v hv j hj σ => ?_⟩
    let j' : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hCA : C j' * (j + 1 : ℕ) ≤ A := by
      dsimp only [A]
      exact (Finset.single_le_sum
        (f := fun l : Fin (n + 1) => C l * (l.val + 1 : ℕ))
        (fun l _ => mul_nonneg (hC l) (Nat.cast_nonneg (l.val + 1)))
        (Finset.mem_univ j')).trans (le_add_of_nonneg_left zero_le_one)
    have hP : (1 + ∑ l, p (t + d j) ((Fin.cons x v : Fin (n + 1) → E) l)) ≤
        1 + ∑ l, p (t + δ) ((Fin.cons x v : Fin (n + 1) → E) l) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun l _ =>
        hp (Nat.add_le_add (Nat.le_refl t) (hd j hj)) _))
    calc
      _ ≤ C j' * tameJetSize p j t (d j) BJ x (v ∘ σ) :=
        hc j' i x hx ((hp hBJ x).trans hbx) (v ∘ σ)
      _ ≤ C j' * ((j + 1 : ℕ) *
          (1 + ∑ l, p (t + d j) ((Fin.cons x v : Fin (n + 1) → E) l))) :=
        mul_le_mul_of_nonneg_left (tameJetSize_selected_unit_le p BJ t (d j) n j x v σ
          (fun l => (hp hBJ _).trans (hv l))) (hC j')
      _ ≤ A * (1 + ∑ l, p (t + δ) ((Fin.cons x v : Fin (n + 1) → E) l)) := by
        rw [← mul_assoc]
        exact mul_le_mul hCA hP (by positivity) (zero_le_one.trans hA)
  obtain ⟨AL, hAL, hlow⟩ := hinner BK
  have hterm (c : OrderedFinpartition n) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ v : Fin n → E,
      (∀ l, p B (v l) ≤ 1) →
      r s (projectiveCompositionTerm (f i) (J i).D (K i).D c x v) ≤
        C * (1 + ∑ l, p (s + L) ((Fin.cons x v : Fin (n + 1) → E) l)) := by
    obtain ⟨AH, hAH, hhigh⟩ := hinner (s + e c.length)
    obtain ⟨CK, hCK, hk⟩ := hK c.length R₀ hR₀ s
    let order : Fin (c.length + 1) → ℕ := Fin.cons (s + e c.length + δ) (fun _ => BK + δ)
    let total : ℕ := s + (e c.length + δ + c.length * (BK + δ))
    have htotal : ∑ j, order j ≤ total := by
      simp only [order, total, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      omega
    obtain ⟨D, hD, hpD⟩ := hproduct n (c.length + 1) order total htotal
      (max R 1) (zero_le_one.trans (le_max_right _ _))
    let A : ℝ := CK * ((c.length : ℝ) + 2) * AH * AL ^ c.length
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg (mul_nonneg (mul_nonneg hCK (by positivity))
        (zero_le_one.trans hAH)) (pow_nonneg (zero_le_one.trans hAL) _)
    refine ⟨A * D, mul_nonneg hA hD, fun i x hx hbx v hv => ?_⟩
    let P : ℕ → ℝ := fun t => 1 + ∑ l, p t ((Fin.cons x v : Fin (n + 1) → E) l)
    have hP (t : ℕ) : 1 ≤ P t := le_add_of_nonneg_right
      (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
    have hmono : Monotone P := fun _ _ h => add_le_add le_rfl
      (Finset.sum_le_sum (fun l _ => hp h _))
    have hb (l : Fin (n + 1)) :
        p BP ((Fin.cons x v : Fin (n + 1) → E) l) ≤ max R 1 := by
      refine Fin.cases ?_ (fun j => ?_) l
      · exact ((hp hBP x).trans hbx).trans (le_max_left _ _)
      · exact ((hp hBP _).trans (hv j)).trans (le_max_right _ _)
    have hprod : P (s + e c.length + δ) * P (BK + δ) ^ c.length ≤
        D * P (s + L) := by
      have hbudget : total + LP ≤ s + L := by
        have := hL c
        dsimp only [termLoss, total] at *
        omega
      have hh := (hpD (Fin.cons x v) hb).trans
        (mul_le_mul_of_nonneg_left (hmono hbudget) hD)
      simpa only [order, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, P] using hh
    have hbase : q (s + e c.length) (f i x) ≤ AH * P (s + e c.length + δ) := by
      have hh := hhigh i x hx hbx v hv 0 (Nat.zero_le n) Fin.elim0
      have hz : v ∘ (Fin.elim0 : Fin 0 → Fin n) = Fin.elim0 := Subsingleton.elim _ _
      simpa only [hz, (J i).zero x hx, P] using hh
    have hsize := tameJetSize_uniform_slots q c.length s (e c.length) BK (f i x)
      (fun j => (J i).D (c.partSize j) x (v ∘ c.emb j))
      (AL * P (BK + δ)) (AH * P (s + e c.length + δ))
      (by simpa only [one_mul] using
        mul_le_mul hAL (hP (BK + δ)) zero_le_one (zero_le_one.trans hAL))
      (by simpa only [one_mul] using
        mul_le_mul hAH (hP (s + e c.length + δ)) zero_le_one (zero_le_one.trans hAH))
      hbase (fun j => hhigh i x hx hbx v hv (c.partSize j) (c.partSize_le j) (c.emb j))
      (fun j => hlow i x hx hbx v hv (c.partSize j) (c.partSize_le j) (c.emb j))
    calc
      _ ≤ CK * tameJetSize q c.length s (e c.length) BK (f i x)
          (fun j => (J i).D (c.partSize j) x (v ∘ c.emb j)) :=
        hk i (f i x) (hmap i hx) (hlowImage i x hx hbx) _
      _ ≤ CK * (((c.length : ℝ) + 2) * (AH * P (s + e c.length + δ)) *
          (AL * P (BK + δ)) ^ c.length) := mul_le_mul_of_nonneg_left hsize hCK
      _ = A * (P (s + e c.length + δ) * P (BK + δ) ^ c.length) := by
        rw [mul_pow]
        dsimp only [A]
        ring
      _ ≤ A * (D * P (s + L)) := mul_le_mul_of_nonneg_left hprod hA
      _ = _ := by dsimp only [P]; ring
  choose C hC hc using hterm
  let K₀ : ℝ := ∑ c, C c
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg (fun c _ => hC c)
  refine ⟨K₀, hK₀, fun i x hx hbx v => ?_⟩
  apply multilinear_bound_of_unitBall
    (projectiveCompositionJets (f i) (J i).D (K i).D n x) (r s)
    (p B) (p (s + L)) hK₀ _ v
  intro w hw
  have hsum (S : Finset (OrderedFinpartition n)) :
      r s (∑ c ∈ S, projectiveCompositionTerm (f i) (J i).D (K i).D c x w) ≤
        ∑ c ∈ S, r s (projectiveCompositionTerm (f i) (J i).D (K i).D c x w) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, map_zero, le_refl]
    | @insert c S hcs ih =>
        simpa only [Finset.sum_insert hcs] using
          (map_add_le_add (r s) _ _).trans (add_le_add le_rfl ih)
  calc
    _ ≤ ∑ c, r s (projectiveCompositionTerm (f i) (J i).D (K i).D c x w) := by
      rw [projectiveCompositionJets_apply]
      exact hsum Finset.univ
    _ ≤ ∑ c, C c * (1 + ∑ l, p (s + L) ((Fin.cons x w : Fin (n + 1) → E) l)) :=
      Finset.sum_le_sum (fun c _ => hc c i x hx hbx w (fun l => (hw l).le))
    _ = K₀ * ((1 + p (s + L) x) + ∑ l, p (s + L) (w l)) := by
      rw [← Finset.sum_mul, Fin.sum_univ_succ]
      simp only [K₀, Fin.cons_zero, Fin.cons_succ, add_assoc]

end ContinuousFlexibility.Analysis
