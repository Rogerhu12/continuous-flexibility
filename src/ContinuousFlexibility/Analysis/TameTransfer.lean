module

public import ContinuousFlexibility.Statements.Analysis
public import ContinuousFlexibility.Analysis.TameLinear

/-!
# Transfer of smoothing operators and smooth tame maps

Closure lemmas for the tame vocabulary of
`ContinuousFlexibility.Statements` (`SmoothTameOn`, `HasSmoothing`,
`pairGrading`, `realGrading`), used in §9 of the paper when the
Nash–Moser theorem is applied on tame direct summands of products and on
smaller neighbourhoods.

* `smoothTameOn_mono`: restriction of a smooth tame map to an open subset.
* `hasSmoothing_pairGrading`, `hasSmoothing_realGrading`: products and `ℝ`.
* `hasSmoothing_submodule`, `hasSmoothing_range`: a subspace which is the
  image of a continuous linear projection that is tame with zero loss above
  some base order.
* `hasSmoothing_ker_rankOne`: the rank-one case `P x = x - ℓ x • ψ`;
  zero loss of `P` is proved only at orders `n ≥ b`, using monotonicity of
  the grading, which suffices because `HasSmoothing` has its own base order.
* `hasSmoothing_transport`, `smoothTameOn_transport`: transport along an
  isometric (for every seminorm) continuous linear equivalence.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators NNReal
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section General

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-! ## 1. Restriction to an open subset -/

/-- Restriction of a tower of directional derivatives to an open subset. -/
def smoothDirectionsRestrict {U V : Set E} {f : E → F} (J : SmoothDirections U f)
    (hV : IsOpen V) (hVU : V ⊆ U) : SmoothDirections V f where
  open_domain := hV
  D := J.D
  zero := fun x hx => J.zero x (hVU hx)
  continuous := fun n =>
    (J.continuous n).mono (Set.prod_mono hVU (subset_refl _))
  derivative := fun n x hx v w => J.derivative n x (hVU hx) v w

theorem smoothTameOn_mono {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U V : Set E} {f : E → F} (h : SmoothTameOn p q U f) (hV : IsOpen V)
    (hVU : V ⊆ U) : SmoothTameOn p q V f := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨smoothDirectionsRestrict J hV hVU, fun k x0 hx0 => ?_⟩
  obtain ⟨loss, base, ε, hε, hs⟩ := hJ k x0 (hVU hx0)
  refine ⟨loss, base, ε, hε, fun s hs' => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hs s hs'
  exact ⟨C, hC0, fun x hx => hC x (hVU hx)⟩

/-! ## 2. Products and the real line -/

private theorem exp_up_mono (a : ℝ) {l L : ℕ} (h : l ≤ L) (N : ℕ) :
    Real.exp ((a + l) * N) ≤ Real.exp ((a + L) * N) := by
  apply Real.exp_le_exp.mpr
  have hl : (l : ℝ) ≤ L := by exact_mod_cast h
  have := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) N)
  linarith

private theorem exp_down_mono (a : ℝ) {l L : ℕ} (h : l ≤ L) (N : ℕ) :
    Real.exp (-(a - l) * N) ≤ Real.exp (-(a - L) * N) := by
  apply Real.exp_le_exp.mpr
  have hl : (l : ℝ) ≤ L := by exact_mod_cast h
  have := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) N)
  linarith

omit [TopologicalSpace E] [TopologicalSpace F] in
private theorem pairGrading_apply (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (n : ℕ) (x : E × F) : pairGrading p q n x = p n x.1 + q n x.2 := by
  simp [pairGrading]

private theorem le_max_mul {A B C1 C2 e1 e2 : ℝ} (hA : 0 ≤ A) (hC1 : 0 ≤ C1)
    (he : e1 ≤ e2) (he1 : 0 ≤ e1) (h : B ≤ C1 * e1 * A) :
    B ≤ max C1 C2 * e2 * A :=
  h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (le_max_left _ _) he he1 (le_max_of_le_left hC1)) hA)

theorem hasSmoothing_pairGrading {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : HasSmoothing p) (hq : HasSmoothing q) : HasSmoothing (pairGrading p q) := by
  obtain ⟨b1, l1, S, h1a, h1b, h1c⟩ := hp
  obtain ⟨b2, l2, T, h2a, h2b, h2c⟩ := hq
  refine ⟨max b1 b2, max l1 l2, fun N => (S N).prodMap (T N), ?_, ?_, ?_⟩
  · intro m n hm hmn
    obtain ⟨C1, hC1, hC1'⟩ := h1a m n (le_of_max_le_left hm) hmn
    obtain ⟨C2, hC2, hC2'⟩ := h2a m n (le_of_max_le_right hm) hmn
    refine ⟨max C1 C2, le_max_of_le_left hC1, fun N x => ?_⟩
    rw [pairGrading_apply, pairGrading_apply, mul_add]
    simp only [ContinuousLinearMap.coe_prodMap', Prod.map_fst, Prod.map_snd]
    have a := le_max_mul (C2 := C2) (apply_nonneg _ _) hC1
      (exp_up_mono ((n : ℝ) - m) (le_max_left l1 l2) N) (Real.exp_pos _).le (hC1' N x.1)
    have b := le_max_mul (C2 := C1) (apply_nonneg _ _) hC2
      (exp_up_mono ((n : ℝ) - m) (le_max_right l1 l2) N) (Real.exp_pos _).le (hC2' N x.2)
    rw [max_comm C2 C1] at b
    exact add_le_add a b
  · intro m n hm hmn
    obtain ⟨C1, hC1, hC1'⟩ := h1b m n (le_of_max_le_left hm) hmn
    obtain ⟨C2, hC2, hC2'⟩ := h2b m n (le_of_max_le_right hm) hmn
    refine ⟨max C1 C2, le_max_of_le_left hC1, fun N x => ?_⟩
    rw [pairGrading_apply, pairGrading_apply, mul_add]
    simp only [ContinuousLinearMap.coe_prodMap', Prod.fst_sub, Prod.snd_sub, Prod.map_fst,
      Prod.map_snd]
    have a := le_max_mul (C2 := C2) (apply_nonneg _ _) hC1
      (exp_down_mono ((n : ℝ) - m) (le_max_left l1 l2) N) (Real.exp_pos _).le (hC1' N x.1)
    have b := le_max_mul (C2 := C1) (apply_nonneg _ _) hC2
      (exp_down_mono ((n : ℝ) - m) (le_max_right l1 l2) N) (Real.exp_pos _).le (hC2' N x.2)
    rw [max_comm C2 C1] at b
    exact add_le_add a b
  · intro x
    exact (h1c x.1).prodMk_nhds (h2c x.2)

theorem hasSmoothing_realGrading : HasSmoothing realGrading := by
  refine ⟨0, 0, fun _ => ContinuousLinearMap.id ℝ ℝ, ?_, ?_, ?_⟩
  · intro m n _ hmn
    refine ⟨1, zero_le_one, fun N x => ?_⟩
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h1 : 1 ≤ Real.exp (((n : ℝ) - m + ((0 : ℕ) : ℝ)) * N) :=
      Real.one_le_exp (mul_nonneg (by simp [hmn']) (Nat.cast_nonneg _))
    simp only [realGrading, ContinuousLinearMap.id_apply, coe_normSeminorm, one_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) h1
  · intro m n _ _
    refine ⟨0, le_refl _, fun N x => ?_⟩
    simp [realGrading]
  · intro x
    exact tendsto_const_nhds

/-! ## 3. Complemented subspaces -/

/-- Smoothing operators pass to a subspace `W` which is the image of a continuous
linear projection `P` (`P x ∈ W`, `P = id` on `W`) that is tame with zero loss
at all orders `n ≥ b0`. The new operators are `P ∘ S_N` restricted to `W`. -/
theorem hasSmoothing_submodule {p : ℕ → Seminorm ℝ E} (W : Submodule ℝ E)
    (P : E →L[ℝ] E) (hPW : ∀ x, P x ∈ W) (hPid : ∀ w ∈ W, P w = w) {b0 : ℕ}
    (hPt : IsTameLinear p p P.toLinearMap 0 b0) (hp : HasSmoothing p) :
    HasSmoothing (fun n => (p n).comp W.subtype) := by
  obtain ⟨base, loss, S, ha, hb, hc⟩ := hp
  let T : ℕ → W →L[ℝ] W := fun N =>
    ((P.comp (S N)).comp W.subtypeL).codRestrict W (fun x => hPW _)
  have hT : ∀ N (w : W), ((T N w : W) : E) = P (S N w) := fun _ _ => rfl
  refine ⟨max base b0, loss, T, ?_, ?_, ?_⟩
  · intro m n hm hmn
    obtain ⟨C, hC0, hC⟩ := ha m n (le_of_max_le_left hm) hmn
    obtain ⟨CP, hCP⟩ := hPt n ((le_of_max_le_right hm).trans hmn)
    refine ⟨CP * C, mul_nonneg CP.2 hC0, fun N w => ?_⟩
    simp only [Seminorm.comp_apply, Submodule.subtype_apply, hT]
    have h1 := hCP (S N w)
    simp only [add_zero, ContinuousLinearMap.coe_coe] at h1
    calc p n (P (S N w)) ≤ CP * p n (S N w) := h1
      _ ≤ CP * (C * Real.exp (((n : ℝ) - m + loss) * N) * p m w) :=
        mul_le_mul_of_nonneg_left (hC N w) CP.2
      _ = CP * C * Real.exp (((n : ℝ) - m + loss) * N) * p m w := by ring
  · intro m n hm hmn
    obtain ⟨C, hC0, hC⟩ := hb m n (le_of_max_le_left hm) hmn
    obtain ⟨CP, hCP⟩ := hPt m (le_of_max_le_right hm)
    refine ⟨CP * C, mul_nonneg CP.2 hC0, fun N w => ?_⟩
    simp only [Seminorm.comp_apply, Submodule.subtype_apply, Submodule.coe_sub, hT]
    have h1 := hCP ((w : E) - S N w)
    simp only [add_zero, ContinuousLinearMap.coe_coe, map_sub, hPid w w.2] at h1
    calc p m ((w : E) - P (S N w)) ≤ CP * p m ((w : E) - S N w) := h1
      _ ≤ CP * (C * Real.exp (-((n : ℝ) - m - loss) * N) * p n w) :=
        mul_le_mul_of_nonneg_left (hC N w) CP.2
      _ = CP * C * Real.exp (-((n : ℝ) - m - loss) * N) * p n w := by ring
  · intro w
    apply tendsto_subtype_rng.mpr
    have h := (P.continuous.tendsto (w : E)).comp (hc (w : E))
    rw [hPid w w.2] at h
    exact h

/-- The range of an idempotent continuous linear map which is tame with zero
loss above `b0` inherits smoothing operators. -/
theorem hasSmoothing_range {p : ℕ → Seminorm ℝ E} (P : E →L[ℝ] E)
    (hP : ∀ x, P (P x) = P x) {b0 : ℕ} (hPt : IsTameLinear p p P.toLinearMap 0 b0)
    (hp : HasSmoothing p) :
    HasSmoothing (fun n => (p n).comp (LinearMap.range (P : E →ₗ[ℝ] E)).subtype) := by
  refine hasSmoothing_submodule (LinearMap.range (P : E →ₗ[ℝ] E)) P
    (fun x => LinearMap.mem_range_self (P : E →ₗ[ℝ] E) x) ?_ hPt hp
  intro w hw
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hw
  exact hP y

/-! ## 4. Transport along a linear homeomorphism preserving every seminorm -/

section Transport

variable {X X' : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace X'] [AddCommGroup X'] [Module ℝ X']

theorem hasSmoothing_transport {p : ℕ → Seminorm ℝ X} {p' : ℕ → Seminorm ℝ X'}
    (Φ : X ≃L[ℝ] X') (hΦ : ∀ n x, p' n (Φ x) = p n x) (hp : HasSmoothing p) :
    HasSmoothing p' := by
  have hΦs : ∀ n y, p n (Φ.symm y) = p' n y := by
    intro n y; rw [← hΦ, Φ.apply_symm_apply]
  obtain ⟨base, loss, S, ha, hb, hc⟩ := hp
  refine ⟨base, loss, fun N =>
    ((Φ : X →L[ℝ] X').comp (S N)).comp (Φ.symm : X' →L[ℝ] X), ?_, ?_, ?_⟩
  · intro m n hm hmn
    obtain ⟨C, hC0, hC⟩ := ha m n hm hmn
    refine ⟨C, hC0, fun N y => ?_⟩
    have h := hC N (Φ.symm y)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hΦ]
    rwa [hΦs] at h
  · intro m n hm hmn
    obtain ⟨C, hC0, hC⟩ := hb m n hm hmn
    refine ⟨C, hC0, fun N y => ?_⟩
    have h := hC N (Φ.symm y)
    have e : y - Φ (S N (Φ.symm y)) = Φ (Φ.symm y - S N (Φ.symm y)) := by
      rw [map_sub, Φ.apply_symm_apply]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [e, hΦ]
    rwa [hΦs] at h
  · intro y
    have h := (Φ.continuous.tendsto _).comp (hc (Φ.symm y))
    rw [Φ.apply_symm_apply] at h
    exact h

theorem hasSmoothing_transport_iff {p : ℕ → Seminorm ℝ X} {p' : ℕ → Seminorm ℝ X'}
    (Φ : X ≃L[ℝ] X') (hΦ : ∀ n x, p' n (Φ x) = p n x) :
    HasSmoothing p ↔ HasSmoothing p' := by
  refine ⟨hasSmoothing_transport Φ hΦ, hasSmoothing_transport Φ.symm ?_⟩
  intro n y; rw [← hΦ, Φ.apply_symm_apply]

/-- Transport of a tower of directional derivatives along a continuous linear
equivalence: `D' n y v = D n (Φ⁻¹ y) (Φ⁻¹ ∘ v)`. -/
def smoothDirectionsTransport {U : Set X} {f : X → F} (J : SmoothDirections U f)
    (Φ : X ≃L[ℝ] X') : SmoothDirections (Φ '' U) (f ∘ Φ.symm) where
  open_domain := by
    rw [Φ.image_eq_preimage_symm]
    exact J.open_domain.preimage Φ.symm.continuous
  D := fun n y => (J.D n (Φ.symm y)).compContinuousLinearMap
    (fun _ => (Φ.symm : X' →L[ℝ] X))
  zero := by
    intro y hy
    rw [Φ.image_eq_preimage_symm] at hy
    have e : (fun i : Fin 0 => (Φ.symm : X' →L[ℝ] X) (Fin.elim0 i)) = Fin.elim0 := by
      funext i; exact i.elim0
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_apply]
    rw [e]
    exact J.zero _ hy
  continuous := by
    intro n
    rw [Φ.image_eq_preimage_symm]
    have hg : Continuous (fun q : X' × (Fin n → X') =>
        ((Φ.symm q.1 : X), fun i => (Φ.symm (q.2 i) : X))) :=
      (Φ.symm.continuous.comp continuous_fst).prodMk
        (continuous_pi fun i => Φ.symm.continuous.comp ((continuous_apply i).comp continuous_snd))
    have hm : MapsTo (fun q : X' × (Fin n → X') =>
        ((Φ.symm q.1 : X), fun i => (Φ.symm (q.2 i) : X)))
        ((Φ.symm ⁻¹' U) ×ˢ (univ : Set (Fin n → X'))) (U ×ˢ univ) :=
      fun q hq => ⟨hq.1, Set.mem_univ _⟩
    exact (J.continuous n).comp hg.continuousOn hm
  derivative := by
    intro n y hy v w
    rw [Φ.image_eq_preimage_symm] at hy
    have h := J.derivative n (Φ.symm y) hy (fun i => Φ.symm (v i)) (Φ.symm w)
    have e : (fun i => (Φ.symm : X' →L[ℝ] X) ((Fin.cons w v : Fin (n + 1) → X') i)) =
        (Fin.cons (Φ.symm w) (fun i => Φ.symm (v i)) : Fin (n + 1) → X) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt at h ⊢
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, e]
    simp only [map_add, map_smul, ContinuousLinearEquiv.coe_coe]
    exact h

@[simp]
theorem smoothDirectionsTransport_D_apply {U : Set X} {f : X → F}
    (J : SmoothDirections U f) (Φ : X ≃L[ℝ] X') (n : ℕ) (y : X') (v : Fin n → X') :
    (smoothDirectionsTransport J Φ).D n y v = J.D n (Φ.symm y) (fun i => Φ.symm (v i)) := rfl

theorem smoothTameOn_transport {p : ℕ → Seminorm ℝ X} {p' : ℕ → Seminorm ℝ X'}
    {q : ℕ → Seminorm ℝ F} (Φ : X ≃L[ℝ] X') (hΦ : ∀ n x, p' n (Φ x) = p n x)
    {U : Set X} {f : X → F} (h : SmoothTameOn p q U f) :
    SmoothTameOn p' q (Φ '' U) (f ∘ Φ.symm) := by
  have hΦs : ∀ n y, p n (Φ.symm y) = p' n y := by
    intro n y; rw [← hΦ, Φ.apply_symm_apply]
  obtain ⟨J, hJ⟩ := h
  refine ⟨smoothDirectionsTransport J Φ, fun k y0 hy0 => ?_⟩
  rw [Φ.image_eq_preimage_symm] at hy0
  obtain ⟨loss, base, ε, hε, hs⟩ := hJ k (Φ.symm y0) hy0
  refine ⟨loss, base, ε, hε, fun s hs' => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hs s hs'
  refine ⟨C, hC0, fun y hy hyε v => ?_⟩
  rw [Φ.image_eq_preimage_symm] at hy
  have hyε' : p base (Φ.symm y - Φ.symm y0) < ε := by
    rw [← map_sub Φ.symm y y0, hΦs]; exact hyε
  have h := hC (Φ.symm y) hy hyε' (fun i => Φ.symm (v i))
  simp only [hΦs] at h
  rw [smoothDirectionsTransport_D_apply]
  exact h

theorem smoothTameOn_transport_iff {p : ℕ → Seminorm ℝ X} {p' : ℕ → Seminorm ℝ X'}
    {q : ℕ → Seminorm ℝ F} (Φ : X ≃L[ℝ] X') (hΦ : ∀ n x, p' n (Φ x) = p n x)
    {U : Set X} {f : X → F} :
    SmoothTameOn p q U f ↔ SmoothTameOn p' q (Φ '' U) (f ∘ Φ.symm) := by
  refine ⟨smoothTameOn_transport Φ hΦ, fun h => ?_⟩
  have hΦs : ∀ n y, p n (Φ.symm y) = p' n y := by
    intro n y; rw [← hΦ, Φ.apply_symm_apply]
  have h2 := smoothTameOn_transport Φ.symm hΦs h
  have e1 : Φ.symm '' (Φ '' U) = U := Φ.symm_image_image U
  have e2 : (f ∘ Φ.symm) ∘ Φ.symm.symm = f := by
    funext x; simp
  rwa [e1, e2] at h2

end Transport

end General

/-! ## 3'. The rank-one projection `P x = x - ℓ x • ψ` -/

section RankOne

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The rank-one projection `x ↦ x - ℓ x • ψ`. -/
def rankOneProjection (ℓ : E →L[ℝ] ℝ) (ψ : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ℓ.smulRight ψ

theorem rankOneProjection_apply (ℓ : E →L[ℝ] ℝ) (ψ : E) (x : E) :
    rankOneProjection ℓ ψ x = x - ℓ x • ψ := by
  simp [rankOneProjection]

/-- If `|ℓ x| ≤ C p_b x` and the grading is monotone, then the rank-one
projection is tame with zero loss at every order `n ≥ b`. (Below `b` this can
fail.) -/
theorem rankOneProjection_isTameLinear {p : ℕ → Seminorm ℝ E} (ℓ : E →L[ℝ] ℝ) (ψ : E)
    (hmono : ∀ m n, m ≤ n → ∀ x, p m x ≤ p n x) {b : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hℓ : ∀ x, |ℓ x| ≤ C * p b x) :
    IsTameLinear p p (rankOneProjection ℓ ψ).toLinearMap 0 b := by
  intro n hn
  refine ⟨⟨1 + C * p n ψ, add_nonneg zero_le_one (mul_nonneg hC (apply_nonneg _ _))⟩,
    fun x => ?_⟩
  have hx : (rankOneProjection ℓ ψ).toLinearMap x = x - ℓ x • ψ :=
    rankOneProjection_apply ℓ ψ x
  show p n ((rankOneProjection ℓ ψ).toLinearMap x) ≤ (1 + C * p n ψ) * p (n + 0) x
  rw [hx, add_zero]
  have h1 := map_sub_le_add (p n) x (ℓ x • ψ)
  rw [map_smul_eq_mul, Real.norm_eq_abs] at h1
  have h2 : |ℓ x| * p n ψ ≤ C * p n x * p n ψ :=
    mul_le_mul_of_nonneg_right ((hℓ x).trans (mul_le_mul_of_nonneg_left (hmono b n hn x) hC))
      (apply_nonneg _ _)
  nlinarith [h1, h2]

/-- Smoothing operators on the hyperplane `ker ℓ`, for a continuous functional
`ℓ` with `ℓ ψ = 1` and `|ℓ x| ≤ C p_b x`, when the grading is monotone. -/
theorem hasSmoothing_ker_rankOne {p : ℕ → Seminorm ℝ E} (ℓ : E →L[ℝ] ℝ) (ψ : E)
    (hℓψ : ℓ ψ = 1) (hmono : ∀ m n, m ≤ n → ∀ x, p m x ≤ p n x) {b : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hℓ : ∀ x, |ℓ x| ≤ C * p b x) (hp : HasSmoothing p) :
    HasSmoothing (fun n => (p n).comp ℓ.toLinearMap.ker.subtype) := by
  refine hasSmoothing_submodule ℓ.toLinearMap.ker (rankOneProjection ℓ ψ) ?_ ?_
    (rankOneProjection_isTameLinear ℓ ψ hmono hC hℓ) hp
  · intro x
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, rankOneProjection_apply, map_sub,
      map_smul, hℓψ, smul_eq_mul, mul_one, sub_self]
  · intro w hw
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hw
    rw [rankOneProjection_apply, hw, zero_smul, sub_zero]

end RankOne

end ContinuousFlexibility.Analysis
