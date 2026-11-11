import ContinuousFlexibility.Analysis.Graded

/-!
# Fixed-loss tame linear estimates and actual continuity

The loss and base order are fixed natural numbers. The estimate holds at
every order above that one base, for all input vectors; only its numerical
constant may depend on the output order. Monotonicity of the target grading
also controls the finitely many lower orders, which proves genuine
continuity for the existing seminorm topologies.

The closure rules below track losses and base orders explicitly. They do
not construct smoothing operators, tame nonlinear calculus, or a
Nash–Moser iteration, and do not instantiate weighted Sobolev operators.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators NNReal

set_option backward.isDefEq.respectTransparency false

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

/-- A standard linear tame estimate with one fixed loss and one fixed
base order. There is no order-dependent neighborhood or restricted input
set: the estimate holds on the whole linear space. -/
def IsTameLinear (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (L : E →ₗ[ℝ] F) (loss base : ℕ) : Prop :=
  ∀ n, base ≤ n → ∃ C : ℝ≥0, ∀ x, q n (L x) ≤ (C : ℝ) * p (n + loss) x

namespace IsTameLinear

variable {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {t : ℕ → Seminorm ℝ G}
  {L M : E →ₗ[ℝ] F} {N : F →ₗ[ℝ] G} {r s b c : ℕ}

/-- Increasing loss or base order preserves the estimate. -/
theorem weaken (hL : IsTameLinear p q L r b) (hp : Monotone p)
    {r' b' : ℕ} (hr : r ≤ r') (hb : b ≤ b') : IsTameLinear p q L r' b' := by
  intro n hn
  obtain ⟨C, hC⟩ := hL n (hb.trans hn)
  refine ⟨C, fun x => (hC x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hp (Nat.add_le_add_left hr n) x) C.coe_nonneg

theorem id (p : ℕ → Seminorm ℝ E) : IsTameLinear p p LinearMap.id 0 0 := by
  intro n _
  exact ⟨1, fun x => by simp⟩

theorem zero (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (r b : ℕ) :
    IsTameLinear p q (0 : E →ₗ[ℝ] F) r b := by
  intro n _
  exact ⟨0, fun x => by simp⟩

theorem smul (hL : IsTameLinear p q L r b) (a : ℝ) :
    IsTameLinear p q (a • L) r b := by
  intro n hn
  obtain ⟨C, hC⟩ := hL n hn
  refine ⟨‖a‖₊ * C, fun x => ?_⟩
  change q n (a • L x) ≤ _
  rw [map_smul_eq_mul]
  calc
    _ ≤ ‖a‖ * ((C : ℝ) * p (n + r) x) :=
      mul_le_mul_of_nonneg_left (hC x) (norm_nonneg a)
    _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring

theorem neg (hL : IsTameLinear p q L r b) : IsTameLinear p q (-L) r b := by
  simpa only [neg_one_smul] using hL.smul (-1)

theorem add (hL : IsTameLinear p q L r b) (hp : Monotone p)
    (hM : IsTameLinear p q M s c) :
    IsTameLinear p q (L + M) (max r s) (max b c) := by
  intro n hn
  obtain ⟨C, hC⟩ := hL n ((le_max_left b c).trans hn)
  obtain ⟨D, hD⟩ := hM n ((le_max_right b c).trans hn)
  refine ⟨C + D, fun x => ?_⟩
  calc
    q n ((L + M) x) ≤ q n (L x) + q n (M x) := map_add_le_add (q n) _ _
    _ ≤ (C : ℝ) * p (n + r) x + (D : ℝ) * p (n + s) x := add_le_add (hC x) (hD x)
    _ ≤ (C : ℝ) * p (n + max r s) x + (D : ℝ) * p (n + max r s) x :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hp (Nat.add_le_add_left (le_max_left r s) n) x) C.coe_nonneg)
        (mul_le_mul_of_nonneg_left (hp (Nat.add_le_add_left (le_max_right r s) n) x) D.coe_nonneg)
    _ = _ := by rw [NNReal.coe_add]; ring

theorem sub (hL : IsTameLinear p q L r b) (hp : Monotone p)
    (hM : IsTameLinear p q M s c) :
    IsTameLinear p q (L - M) (max r s) (max b c) := by
  simpa only [sub_eq_add_neg] using hL.add hp hM.neg

/-- Composition adds the fixed losses. The maximum of the two original
base orders is a sufficient common base for the whole composition. -/
theorem comp (hN : IsTameLinear q t N s c) (hL : IsTameLinear p q L r b) :
    IsTameLinear p t (N.comp L) (r + s) (max b c) := by
  intro n hn
  obtain ⟨D, hD⟩ := hN n ((le_max_right b c).trans hn)
  obtain ⟨C, hC⟩ := hL (n + s)
    (((le_max_left b c).trans hn).trans (Nat.le_add_right n s))
  refine ⟨D * C, fun x => ?_⟩
  calc
    t n ((N.comp L) x) ≤ (D : ℝ) * q (n + s) (L x) := hD (L x)
    _ ≤ (D : ℝ) * ((C : ℝ) * p ((n + s) + r) x) :=
      mul_le_mul_of_nonneg_left (hC x) D.coe_nonneg
    _ = _ := by
      rw [NNReal.coe_mul, Nat.add_assoc, Nat.add_comm s r]
      ring

theorem sum {ι : Type*} (S : Finset ι) (Ls : ι → E →ₗ[ℝ] F) (hp : Monotone p)
    (hL : ∀ i ∈ S, IsTameLinear p q (Ls i) r b) :
    IsTameLinear p q (S.sum Ls) r b := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using zero p q r b
  | @insert i S hi ih =>
    have hhead := hL i (Finset.mem_insert_self i S)
    have htail := ih (fun j hj => hL j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi, max_self] using hhead.add hp htail

/-- A fixed tame estimate controls every target seminorm. For an output
order below the base, monotonicity uses the single level `max n base`. -/
theorem isBounded (hL : IsTameLinear p q L r b) (hq : Monotone q) :
    Seminorm.IsBounded p q L := by
  intro n
  obtain ⟨C, hC⟩ := hL (max n b) (le_max_right n b)
  refine ⟨{max n b + r}, C, ?_⟩
  rw [Finset.sup_singleton]
  intro x
  exact (hq (le_max_left n b) (L x)).trans (hC x)

theorem continuous [TopologicalSpace E] [TopologicalSpace F]
    (hL : IsTameLinear p q L r b) (hp : WithSeminorms p) (hq : WithSeminorms q)
    (hqmono : Monotone q) : Continuous L :=
  hp.continuous_of_isBounded hq L (hL.isBounded hqmono)

/-- Package the same underlying linear map with the continuity just
proved from its tame estimate. -/
def toContinuousLinearMap [TopologicalSpace E] [TopologicalSpace F]
    (hL : IsTameLinear p q L r b) (hp : WithSeminorms p) (hq : WithSeminorms q)
    (hqmono : Monotone q) : E →L[ℝ] F where
  toLinearMap := L
  cont := hL.continuous hp hq hqmono

@[simp] theorem toContinuousLinearMap_apply [TopologicalSpace E] [TopologicalSpace F]
    (hL : IsTameLinear p q L r b) (hp : WithSeminorms p) (hq : WithSeminorms q)
    (hqmono : Monotone q) (x : E) : hL.toContinuousLinearMap hp hq hqmono x = L x := rfl

end IsTameLinear

section FiniteProduct

variable {ι : Type*} [Fintype ι] {X : ι → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]

/-- A finite direct product is graded by the maximum of its coordinate
seminorms at the same order. -/
def finiteProductGrading (q : ∀ i, ℕ → Seminorm ℝ (X i)) (n : ℕ) :
    Seminorm ℝ (∀ i, X i) :=
  Finset.univ.sup (fun i => (q i n).comp (LinearMap.proj i))

theorem finiteProductGrading_monotone (q : ∀ i, ℕ → Seminorm ℝ (X i))
    (hq : ∀ i, Monotone (q i)) : Monotone (finiteProductGrading q) := by
  intro m n hmn
  apply Finset.sup_mono_fun
  intro i _ x
  exact hq i hmn (x i)

/-- The finite-product grading generates the actual product topology. -/
theorem withSeminorms_finiteProduct [∀ i, TopologicalSpace (X i)]
    {q : ∀ i, ℕ → Seminorm ℝ (X i)} (hq : ∀ i, WithSeminorms (q i)) :
    WithSeminorms (finiteProductGrading q) := by
  classical
  apply (withSeminorms_pi hq).congr
  · intro n
    refine ⟨Finset.univ.image (fun i => (⟨i, n⟩ : Σ _ : ι, ℕ)), 1, ?_⟩
    rw [one_smul, Seminorm.comp_id, Finset.sup_image]
    exact le_rfl
  · intro z
    refine ⟨{z.2}, 1, ?_⟩
    rw [Finset.sup_singleton, one_smul, Seminorm.comp_id]
    exact Finset.le_sup (f := fun i => (q i z.2).comp (LinearMap.proj i))
      (Finset.mem_univ z.1)

/-- A finite family with individual fixed losses and bases has a tame
direct product, with their finite maxima as common loss and base. -/
theorem IsTameLinear.pi {p : ℕ → Seminorm ℝ E}
    {q : ∀ i, ℕ → Seminorm ℝ (X i)} (Ls : ∀ i, E →ₗ[ℝ] X i)
    (loss base : ι → ℕ) (hp : Monotone p)
    (hL : ∀ i, IsTameLinear p (q i) (Ls i) (loss i) (base i)) :
    IsTameLinear p (finiteProductGrading q) (LinearMap.pi Ls)
      (Finset.univ.sup loss) (Finset.univ.sup base) := by
  classical
  intro n hn
  have hi (i : ι) : base i ≤ n := (Finset.le_sup (Finset.mem_univ i)).trans hn
  choose C hC using fun i => hL i n (hi i)
  refine ⟨Finset.univ.sup C, fun x => ?_⟩
  apply Seminorm.finset_sup_apply_le
    (mul_nonneg (NNReal.coe_nonneg _) (apply_nonneg _ _))
  intro i _
  change q i n (Ls i x) ≤ _
  calc
    _ ≤ (C i : ℝ) * p (n + loss i) x := hC i x
    _ ≤ (C i : ℝ) * p (n + Finset.univ.sup loss) x :=
      mul_le_mul_of_nonneg_left
        (hp (Nat.add_le_add_left (Finset.le_sup (Finset.mem_univ i)) n) x) (C i).coe_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (show (C i : ℝ) ≤ (Finset.univ.sup C : ℝ≥0) from
        by exact_mod_cast (Finset.le_sup (Finset.mem_univ i) : C i ≤ Finset.univ.sup C))
      (apply_nonneg _ _)

/-- The actual finite-product coordinate projection has zero loss and
zero base for these maximum gradings. -/
theorem finiteProductProjection_isTame (q : ∀ i, ℕ → Seminorm ℝ (X i)) (i : ι) :
    IsTameLinear (finiteProductGrading q) (q i) (LinearMap.proj i) 0 0 := by
  intro n _
  refine ⟨1, fun x => ?_⟩
  change q i n (x i) ≤ (1 : ℝ) * finiteProductGrading q (n + 0) x
  simp only [Nat.add_zero, one_mul]
  exact Seminorm.le_finset_sup_apply
    (p := fun j => (q j n).comp (LinearMap.proj (φ := X) j)) (x := x) (Finset.mem_univ i)

/-- A finite direct sum of tame operators has the finite maxima of their
losses and bases. The map is the actual coordinatewise linear map. -/
theorem IsTameLinear.piMap {Y : ι → Type*}
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℝ (Y i)]
    {p : ∀ i, ℕ → Seminorm ℝ (X i)} {q : ∀ i, ℕ → Seminorm ℝ (Y i)}
    (Ls : ∀ i, X i →ₗ[ℝ] Y i) (loss base : ι → ℕ)
    (hp : ∀ i, Monotone (p i))
    (hL : ∀ i, IsTameLinear (p i) (q i) (Ls i) (loss i) (base i)) :
    IsTameLinear (finiteProductGrading p) (finiteProductGrading q) (LinearMap.piMap Ls)
      (Finset.univ.sup loss) (Finset.univ.sup base) := by
  have hcomp (i : ι) : IsTameLinear (finiteProductGrading p) (q i)
      ((Ls i).comp (LinearMap.proj i)) (loss i) (base i) := by
    simpa using (hL i).comp (finiteProductProjection_isTame p i)
  exact IsTameLinear.pi (fun i => (Ls i).comp (LinearMap.proj i)) loss base
    (finiteProductGrading_monotone p hp) hcomp

end FiniteProduct

section ProjectiveLimit

variable (X : ℕ → Type*) [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace ℝ (X n)]
  (bx : ∀ n, X (n + 1) →L[ℝ] X n)
  (Y : ℕ → Type*) [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
  (byMap : ∀ n, Y (n + 1) →L[ℝ] Y n)

/-- The generic estimate implies actual continuity between the previously
constructed projective limits with their existing topologies. -/
theorem continuous_projectiveLimit_of_tame
    (L : ProjectiveLimit X bx →ₗ[ℝ] ProjectiveLimit Y byMap) {loss base : ℕ}
    (hL : IsTameLinear (gradedSeminorm X bx) (gradedSeminorm Y byMap) L loss base) :
    Continuous L :=
  hL.continuous (withSeminorms_graded X bx) (withSeminorms_graded Y byMap)
    (gradedSeminorm_monotone Y byMap)

/-- The actual level projection is tame with zero loss above its level. -/
theorem projectiveCoordinate_isTame (k : ℕ) :
    IsTameLinear (gradedSeminorm X bx) (fun _ => normSeminorm ℝ (X k))
      (projectiveCoordinate X bx k).toLinearMap 0 k := by
  intro n hn
  refine ⟨1, fun x => ?_⟩
  change ‖x.1 k‖ ≤ (1 : ℝ) * gradedSeminorm X bx (n + 0) x
  simpa only [Nat.add_zero, one_mul] using norm_coordinate_le_graded X bx hn x

end ProjectiveLimit

end ContinuousFlexibility.Analysis
