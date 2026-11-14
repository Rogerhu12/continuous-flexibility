module

public import ContinuousFlexibility.Scalar.WeightedTowerCalculus
public import ContinuousFlexibility.Analysis.TameJetComposition
public import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Fixed-loss bounds for the actual partition composition tower

All increment directions are first restricted to the unit ball of one fixed
low seminorm.  Every low inner jet is then uniformly bounded; only one high
inner jet occurs in each summand of the outer tame estimate.  Multilinear
normalization recovers the exact homogeneous one-high-factor estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section Estimates

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
  {U : Set X} {V : Set Y} {f : X → Y} {g : Y → Z}
  {b c ell m : ℕ}

/-- On unit low-seminorm directions, a uniform tame estimate is affine in the
high base-point seminorm and the sum of high direction seminorms. -/
theorem UniformScalarTowerEstimate.joint_unit_bound
    {J : SmoothDirections U f}
    (hJ : UniformScalarTowerEstimate p q U b ell f J) (k s : ℕ) (hs : b ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin k → X,
      (∀ i, p b (v i) ≤ 1) →
      q s (J.D k x v) ≤ C * ((1 + p (s + ell) x) + ∑ i, p (s + ell) (v i)) := by
  obtain ⟨C, hC, hCx⟩ := hJ k s hs
  refine ⟨C, hC, fun x hx v hv => (hCx x hx v).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  simpa only [tameJetSize, multilinearTameSize] using
    multilinearTameSize_le_affine (p b) (p (s + ell)) k
      (by positivity : 0 ≤ 1 + p (s + ell) x) v hv

private theorem selected_seminorm_sum
    (P : Seminorm ℝ X) {n k : ℕ} (a : Fin k → Fin n) (v : Fin n → X) :
    (∑ i, P (v (a i))) ≤ (k : ℝ) * ∑ j, P (v j) := by
  calc
    _ ≤ ∑ _i : Fin k, ∑ j, P (v j) :=
      Finset.sum_le_sum (fun i _ => Finset.single_le_sum
        (fun j _ => apply_nonneg _ _) (Finset.mem_univ (a i)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]

private theorem scalar_size_le_scaled
    {k : ℕ} (low high : Seminorm ℝ Y) (w : Fin k → Y)
    {a B G : ℝ} {L H : Fin k → ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hL : ∀ i, 0 ≤ L i) (hH : ∀ i, 0 ≤ H i)
    (ha : a ≤ B * G) (hlow : ∀ i, low (w i) ≤ L i)
    (hhigh : ∀ i, high (w i) ≤ H i * G) :
    multilinearTameSize low high k a w ≤
      (B * ∏ i, L i + ∑ i, H i * ∏ j ∈ Finset.univ.erase i, L j) * G := by
  classical
  have hprod (I : Finset (Fin k)) : (∏ i ∈ I, low (w i)) ≤ ∏ i ∈ I, L i :=
    Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _) (fun i _ => hlow i)
  unfold multilinearTameSize
  calc
    _ ≤ (B * G) * (∏ i, L i) +
        ∑ i, (H i * G) * ∏ j ∈ Finset.univ.erase i, L j :=
      add_le_add
        (mul_le_mul ha (hprod Finset.univ)
          (Finset.prod_nonneg (fun i _ => apply_nonneg _ _)) (mul_nonneg hB hG))
        (Finset.sum_le_sum (fun i _ =>
          mul_le_mul (hhigh i) (hprod (Finset.univ.erase i))
            (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)) (mul_nonneg (hH i) hG)))
    _ = _ := by
      rw [add_mul, Finset.sum_mul]
      apply congrArg₂ (fun x y : ℝ => x + y)
      · ring
      · apply Finset.sum_congr rfl
        intro i _
        ring

/-- One actual ordered-partition term has affine high-order growth on the
common low unit box.  The low base-point bound is fixed before the arity. -/
theorem uniformScalarCompositionTerm_joint_bound
    (hp : Monotone p) (hq : Monotone q)
    (J : SmoothDirections U f) (K : SmoothDirections V g)
    (hJ : UniformScalarTowerEstimate p q U b ell f J)
    (hK : UniformScalarTowerEstimate q r V c m g K)
    (hmap : MapsTo f U V) {R : ℝ} (hR : 0 ≤ R)
    (hxR : ∀ x ∈ U, p (max b c + ell) x ≤ R)
    {n : ℕ} (part : OrderedFinpartition n) (s : ℕ) (hs : max b c + ell ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Fin n → X,
      (∀ i, p (max b c + ell) (v i) < 1) →
      r s (projectiveCompositionTerm f J.D K.D part x v) ≤
        C * ((1 + p (s + (ell + m)) x) + ∑ i, p (s + (ell + m)) (v i)) := by
  classical
  have hb : b ≤ max b c := le_max_left _ _
  have hc : c ≤ max b c := le_max_right _ _
  have hbs : b ≤ s + m := by omega
  have hcs : c ≤ s := by omega
  obtain ⟨C0, hC0, hf0⟩ := hJ.joint_unit_bound 0 (s + m) hbs
  have hlo (i : Fin part.length) := hJ.joint_unit_bound (part.partSize i) (max b c) hb
  choose L hL hLbound using hlo
  have hhi (i : Fin part.length) := hJ.joint_unit_bound (part.partSize i) (s + m) hbs
  choose H hH hHbound using hhi
  obtain ⟨CK, hCK, hKbound⟩ := hK part.length s hcs
  let LB (i : Fin part.length) : ℝ := L i * (1 + R + (part.partSize i : ℝ))
  let HB (i : Fin part.length) : ℝ := H i * (1 + (part.partSize i : ℝ))
  have hLB (i : Fin part.length) : 0 ≤ LB i :=
    mul_nonneg (hL i) (by positivity)
  have hHB (i : Fin part.length) : 0 ≤ HB i :=
    mul_nonneg (hH i) (by positivity)
  let A : ℝ := (1 + C0) * ∏ i, LB i +
    ∑ i, HB i * ∏ j ∈ Finset.univ.erase i, LB j
  have hA : 0 ≤ A := add_nonneg
    (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => hLB i)))
    (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (hHB i) (Finset.prod_nonneg (fun j _ => hLB j))))
  refine ⟨CK * A, mul_nonneg hCK hA, ?_⟩
  intro x hx v hv
  let G : ℝ := (1 + p (s + (ell + m)) x) + ∑ i, p (s + (ell + m)) (v i)
  have hsum : 0 ≤ ∑ i, p (s + (ell + m)) (v i) :=
    Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
  have hG1 : 1 ≤ G :=
    (le_add_of_nonneg_right (apply_nonneg (p (s + (ell + m))) x)).trans
      (le_add_of_nonneg_right hsum)
  have hG : 0 ≤ G := zero_le_one.trans hG1
  have hpx : 0 ≤ 1 + p (s + (ell + m)) x := by positivity
  have hidx : s + m + ell = s + (ell + m) := by omega
  let w : Fin part.length → Y := fun i => J.D (part.partSize i) x (v ∘ part.emb i)
  have hunit (i : Fin part.length) (j : Fin (part.partSize i)) :
      p b ((v ∘ part.emb i) j) ≤ 1 :=
    (hp (by omega : b ≤ max b c + ell) (v (part.emb i j))).trans (hv _).le
  have hlow (i : Fin part.length) : q c (w i) ≤ LB i := by
    have hsumlow : (∑ j : Fin (part.partSize i),
        p (max b c + ell) ((v ∘ part.emb i) j)) ≤ (part.partSize i : ℝ) := by
      calc
        _ ≤ ∑ _j : Fin (part.partSize i), (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => (hv (part.emb i j)).le)
        _ = _ := by simp
    exact (hq hc (w i)).trans ((hLbound i x hx (v ∘ part.emb i) (hunit i)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (le_refl 1) (hxR x hx)) hsumlow) (hL i)))
  have hhigh (i : Fin part.length) : q (s + m) (w i) ≤ HB i * G := by
    have hi := hHbound i x hx (v ∘ part.emb i) (hunit i)
    have hselect := selected_seminorm_sum (p (s + (ell + m))) (part.emb i) v
    have hjoint :
        ((1 + p (s + m + ell) x) + ∑ j, p (s + m + ell) ((v ∘ part.emb i) j)) ≤
          (1 + (part.partSize i : ℝ)) * G := by
      rw [hidx]
      have hm : 0 ≤ (part.partSize i : ℝ) := Nat.cast_nonneg _
      have hgrow :
          (1 + p (s + (ell + m)) x) +
              (part.partSize i : ℝ) * ∑ j, p (s + (ell + m)) (v j) ≤
            (1 + (part.partSize i : ℝ)) * G := by
        dsimp only [G]
        nlinarith [mul_nonneg hm hpx]
      exact (add_le_add (le_refl _) hselect).trans hgrow
    exact hi.trans ((mul_le_mul_of_nonneg_left hjoint (hH i)).trans_eq (by
      dsimp only [HB]
      ring))
  have hfhigh : 1 + q (s + m) (f x) ≤ (1 + C0) * G := by
    have hf := hf0 x hx Fin.elim0 (fun i => Fin.elim0 i)
    rw [J.zero x hx] at hf
    simp only [Fin.sum_univ_zero, add_zero, hidx] at hf
    have hbase : 1 + p (s + (ell + m)) x ≤ G := le_add_of_nonneg_right hsum
    have hfG := hf.trans (mul_le_mul_of_nonneg_left hbase hC0)
    nlinarith
  have hsize : tameJetSize q part.length s m c (f x) w ≤ A * G := by
    simpa only [tameJetSize, multilinearTameSize, A] using
      scalar_size_le_scaled (q c) (q (s + m)) w
        (by positivity : 0 ≤ 1 + C0) hG hLB hHB hfhigh hlow hhigh
  exact ((hKbound (f x) (hmap hx) w).trans
    (mul_le_mul_of_nonneg_left hsize hCK)).trans_eq (by ring)

private theorem composition_seminorm_sum_le
    {ι : Type*} (P : Seminorm ℝ Z) (I : Finset ι) (z : ι → Z) :
    P (∑ i ∈ I, z i) ≤ ∑ i ∈ I, P (z i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add _ _ _).trans (add_le_add (le_refl _) ih)

/-- The actual partition sum satisfies a uniform one-high-factor estimate.
The base is increased once, and the two fixed losses are added once. -/
theorem uniformScalarCompositionJets_bound
    (hp : Monotone p) (hq : Monotone q)
    (J : SmoothDirections U f) (K : SmoothDirections V g)
    (hJ : UniformScalarTowerEstimate p q U b ell f J)
    (hK : UniformScalarTowerEstimate q r V c m g K)
    (hmap : MapsTo f U V) {R : ℝ} (hR : 0 ≤ R)
    (hxR : ∀ x ∈ U, p (max b c + ell) x ≤ R) :
    ∀ n s : ℕ, max b c + ell ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U, ∀ v : Fin n → X,
        r s (projectiveCompositionJets f J.D K.D n x v) ≤
          C * tameJetSize p n s (ell + m) (max b c + ell) x v := by
  classical
  intro n s hs
  have hterms (part : OrderedFinpartition n) :=
    uniformScalarCompositionTerm_joint_bound hp hq J K hJ hK hmap hR hxR part s hs
  choose C hC hCx using hterms
  let B : ℝ := ∑ part, C part
  have hB : 0 ≤ B := Finset.sum_nonneg (fun part _ => hC part)
  refine ⟨multilinearNormalizationConstant n 1 B,
    multilinearNormalizationConstant_nonneg n zero_lt_one hB, ?_⟩
  intro x hx v
  have hlocal : ∀ w : Fin n → X, (∀ i, p (max b c + ell) (w i) < 1) →
      r s (projectiveCompositionJets f J.D K.D n x w) ≤
        B * ((1 + p (s + (ell + m)) x) + ∑ i, p (s + (ell + m)) (w i)) := by
    intro w hw
    rw [projectiveCompositionJets_apply]
    apply (composition_seminorm_sum_le (r s) Finset.univ
      (fun part => projectiveCompositionTerm f J.D K.D part x w)).trans
    change (∑ part, r s (projectiveCompositionTerm f J.D K.D part x w)) ≤
      (∑ part, C part) *
        ((1 + p (s + (ell + m)) x) + ∑ i, p (s + (ell + m)) (w i))
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun part _ => hCx part x hx w hw)
  simpa only [tameJetSize, multilinearTameSize] using
    multilinear_oneHighFactor_of_local (projectiveCompositionJets f J.D K.D n x)
      (r s) (p (max b c + ell)) (p (s + (ell + m))) zero_lt_one hB hlocal v

end Estimates

end ContinuousFlexibility.Statements
