import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsFinite
import ContinuousFlexibility.Analysis.FiniteInversePolynomialEnvelope
import ContinuousFlexibility.Analysis.PolynomialJetOperations

/-!
# Uniform finite coefficient bounds for the actual scalar inverse

The first inverse differential is computed from the scalar slope of the
forward kernel.  The existing nonlinear inverse polynomial then bounds
every higher inverse differential using only forward derivatives and
that scalar denominator.  Its numerical coefficient and exponent are
selected before the kernel, coefficient domain, and evaluation point.

Together with the preceding actual inverse tower and its partition
formula, these are the finite coefficient estimates required to retain
uniform component envelopes after pulling back to the original state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

section TriangularDifferential

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The inverse of the derivative of `(a,r) ↦ (a,F(a,r))`. -/
def n04PositiveGeometry_scalarTriangularInverse (A : (P × ℝ) →L[ℝ] ℝ) :
    (P × ℝ) →L[ℝ] (P × ℝ) :=
  (ContinuousLinearMap.fst ℝ P ℝ).prod
    ((A (0, 1))⁻¹ • (ContinuousLinearMap.snd ℝ P ℝ -
      A.comp ((ContinuousLinearMap.inl ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ P ℝ))))

theorem n04PositiveGeometry_scalarTriangularInverse_apply
    (A : (P × ℝ) →L[ℝ] ℝ) (v : P × ℝ) :
    n04PositiveGeometry_scalarTriangularInverse A v =
      (v.1, (A (0, 1))⁻¹ * (v.2 - A (v.1, 0))) := by
  simp only [n04PositiveGeometry_scalarTriangularInverse, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply, smul_eq_mul]

theorem n04PositiveGeometry_scalarTriangularInverse_left
    (A : (P × ℝ) →L[ℝ] ℝ) (hA : A (0, 1) ≠ 0) :
    (n04PositiveGeometry_scalarTriangularInverse A).comp
      ((ContinuousLinearMap.fst ℝ P ℝ).prod A) = ContinuousLinearMap.id ℝ (P × ℝ) := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = (v.1, 0) + v.2 • ((0, 1) : P × ℝ) := by
    ext <;> simp only [Prod.mk_add_mk, Prod.smul_mk, smul_zero, smul_eq_mul,
      mul_one, add_zero, zero_add]
  have he : A v = A (v.1, 0) + v.2 * A (0, 1) := by
    calc
      A v = A ((v.1, 0) + v.2 • ((0, 1) : P × ℝ)) := congrArg A hv
      _ = _ := by rw [map_add, map_smul, smul_eq_mul]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.id_apply,
    n04PositiveGeometry_scalarTriangularInverse_apply]
  apply Prod.ext
  · rfl
  · rw [he, add_sub_cancel_left]
    field_simp [hA]

theorem n04PositiveGeometry_scalarTriangularInverse_norm
    (A : (P × ℝ) →L[ℝ] ℝ) :
    ‖n04PositiveGeometry_scalarTriangularInverse A‖ ≤
      1 + |(A (0, 1))⁻¹| * (1 + ‖A‖) := by
  have hC : 0 ≤ 1 + |(A (0, 1))⁻¹| * (1 + ‖A‖) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  rw [n04PositiveGeometry_scalarTriangularInverse_apply, Prod.norm_def,
    Real.norm_eq_abs, abs_mul]
  have hAv : |A (v.1, 0)| ≤ ‖A‖ * ‖v‖ := by
    have hpair : ‖((v.1, 0) : P × ℝ)‖ ≤ ‖v‖ := by
      simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)] using norm_fst_le v
    exact (A.le_opNorm (v.1, 0)).trans
      (mul_le_mul_of_nonneg_left hpair (norm_nonneg A))
  have hsub : |v.2 - A (v.1, 0)| ≤ (1 + ‖A‖) * ‖v‖ := by
    have hs : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
    exact (abs_sub _ _).trans ((add_le_add hs hAv).trans_eq (by ring))
  apply max_le
  · have hcoef : 1 ≤ 1 + |(A (0, 1))⁻¹| * (1 + ‖A‖) := by positivity
    exact (norm_fst_le v).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (norm_nonneg v))
  · exact (mul_le_mul_of_nonneg_left hsub (abs_nonneg _)).trans (by
      nlinarith only [norm_nonneg v])

private theorem scalarTriangularInverse_common_bound
    (A : (P × ℝ) →L[ℝ] ℝ) {M : ℝ} (hM : 1 ≤ M)
    (hA : ‖A‖ ≤ M) (hb : |(A (0, 1))⁻¹| ≤ M) :
    ‖n04PositiveGeometry_scalarTriangularInverse A‖ ≤ 3 * M ^ 2 := by
  have hp : |(A (0, 1))⁻¹| * (1 + ‖A‖) ≤ M * (1 + M) :=
    mul_le_mul hb (add_le_add le_rfl hA) (by positivity) (zero_le_one.trans hM)
  apply (n04PositiveGeometry_scalarTriangularInverse_norm A).trans
  have hM2 : M ≤ M ^ 2 := by nlinarith only [hM]
  nlinarith only [hp, hM, hM2]

end TriangularDifferential

section ActualInverseEnvelope

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

/-- A universal finite positive-order bound for the actual inverse of a
scalar coefficient kernel.  The input bound covers only the reciprocal
of the forward scalar slope and the positive forward jets through the
requested order.  Inverse regularity and all higher inverse bounds are
conclusions of the construction. -/
theorem n04PositiveGeometry_scalarInverse_jet_envelope (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ {V : Set P} {F : P × ℝ → ℝ},
        IsOpen V → ContDiffOn ℝ ∞ F (V ×ˢ univ) →
        (∀ a ∈ V, ∀ r, 0 < deriv (fun t => F (a, t)) r) →
        (∀ a ∈ V, Function.Surjective (fun t => F (a, t))) →
      ∀ {M : ℝ}, 1 ≤ M → ∀ q : P × ℝ, q ∈ V ×ˢ univ →
        let G := fun z : P × ℝ => Function.invFun (fun t => F (z.1, t)) z.2
        |(deriv (fun t => F (q.1, t)) (G q))⁻¹| ≤ M →
        (∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
          ‖iteratedFDeriv ℝ k F (q.1, G q)‖ ≤ M) →
        ‖iteratedFDeriv ℝ (n + 1) G q‖ ≤ C * M ^ d := by
  obtain ⟨C, hC, d, hb⟩ :=
    exists_nonlinearInverse_finiteJet_polynomial_envelope (E := P × ℝ) (F := P × ℝ) n
  refine ⟨C * 3 ^ d, mul_pos (zero_lt_one.trans_le hC) (by positivity), 2 * d, ?_⟩
  intro V F hV hF hpositive hsurj M hM q hq G hslope hraw
  let f : P × ℝ → P × ℝ := fun z => (z.1, F z)
  let g : P × ℝ → P × ℝ := fun z => (z.1, G z)
  have hG : ContDiffOn ℝ ∞ G (V ×ˢ univ) :=
    n04PositiveGeometry_scalarInverse_contDiffOn hV hF hpositive hsurj
  have hGq : ContDiffAt ℝ ∞ G q := hG.contDiffAt ((hV.prod isOpen_univ).mem_nhds hq)
  have hFq : ContDiffAt ℝ ∞ F (q.1, G q) :=
    hF.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq.1, mem_univ _⟩)
  have hf : ContDiffAt ℝ ∞ f (g q) := contDiffAt_fst.prodMk hFq
  have hg : ContDiffAt ℝ ∞ g q := contDiffAt_fst.prodMk hGq
  have hfg : f ∘ g =ᶠ[𝓝 q] (id : P × ℝ → P × ℝ) := by
    filter_upwards [(hV.prod isOpen_univ).mem_nhds hq] with z hz
    exact Prod.ext rfl (Function.rightInverse_invFun (hsurj z.1 hz.1) z.2)
  let A : (P × ℝ) →L[ℝ] ℝ := fderiv ℝ F (q.1, G q)
  have hderiv : deriv (fun t => F (q.1, t)) (G q) = A (0, 1) := by
    have hpair : HasDerivAt (fun t : ℝ => (q.1, t)) (0, 1) (G q) :=
      (hasDerivAt_const (G q) q.1).prodMk (hasDerivAt_id (G q))
    have he := (hFq.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (G q) hpair
    exact he.deriv
  have hApos : 0 < A (0, 1) := (hpositive q.1 hq.1 (G q)).trans_eq hderiv
  have hA : ‖A‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_one] using hraw 1 le_rfl (by omega)
  have hAslope : |(A (0, 1))⁻¹| ≤ M := by rwa [hderiv] at hslope
  let L := n04PositiveGeometry_scalarTriangularInverse A
  have hL : L.comp (fderiv ℝ f (g q)) = ContinuousLinearMap.id ℝ (P × ℝ) := by
    have hfd : fderiv ℝ f (g q) = (ContinuousLinearMap.fst ℝ P ℝ).prod A :=
      (hasFDerivAt_fst.prodMk (hFq.differentiableAt (by simp)).hasFDerivAt).fderiv
    rw [hfd]
    exact n04PositiveGeometry_scalarTriangularInverse_left A hApos.ne'
  have hLb : ‖L‖ ≤ 3 * M ^ 2 := scalarTriangularInverse_common_bound A hM hA hAslope
  have hM' : 1 ≤ 3 * M ^ 2 := by nlinarith only [hM]
  have hraw' (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      ‖iteratedFDeriv ℝ (k + 1) f (g q)‖ ≤ 3 * M ^ 2 := by
    rw [iteratedFDeriv_prodMk (contDiffAt_fst : ContDiffAt ℝ ∞ Prod.fst (g q))
      hFq (by simp), ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact ((norm_iteratedFDeriv_linear_of_pos (ContinuousLinearMap.fst ℝ P ℝ)
        (k + 1) (by omega) (g q)).trans (ContinuousLinearMap.norm_fst_le ℝ P ℝ)).trans hM'
    · exact (hraw (k + 1) (by omega) (by omega)).trans (by nlinarith only [hM])
  have hjet := hb hM' f g q hf hg hfg L hL hLb hraw'
  have hproject := (ContinuousLinearMap.snd ℝ P ℝ).norm_iteratedFDeriv_comp_left hg
    (n := n + 1) (by simp)
  have hGjet : ‖iteratedFDeriv ℝ (n + 1) G q‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) g q‖ := by
    exact hproject.trans (mul_le_of_le_one_left (norm_nonneg _)
      (ContinuousLinearMap.norm_snd_le ℝ P ℝ))
  apply hGjet.trans (hjet.trans_eq ?_)
  rw [mul_pow, ← pow_mul]
  ring

/-- A single numerical polynomial controls a finite prefix of positive
inverse jets.  It is selected before the forward family and its bound. -/
theorem n04PositiveGeometry_scalarInverse_jet_prefix_envelope (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ {V : Set P} {F : P × ℝ → ℝ},
        IsOpen V → ContDiffOn ℝ ∞ F (V ×ˢ univ) →
        (∀ a ∈ V, ∀ r, 0 < deriv (fun t => F (a, t)) r) →
        (∀ a ∈ V, Function.Surjective (fun t => F (a, t))) →
      ∀ {M : ℝ}, 1 ≤ M → ∀ q : P × ℝ, q ∈ V ×ˢ univ →
        let G := fun z : P × ℝ => Function.invFun (fun t => F (z.1, t)) z.2
        |(deriv (fun t => F (q.1, t)) (G q))⁻¹| ≤ M →
        (∀ k : ℕ, 1 ≤ k → k ≤ N →
          ‖iteratedFDeriv ℝ k F (q.1, G q)‖ ≤ M) →
        ∀ k : ℕ, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k G q‖ ≤ C * M ^ d := by
  classical
  choose C hC d hb using fun j : Fin N =>
    n04PositiveGeometry_scalarInverse_jet_envelope (P := P) j.val
  let C₀ : ℝ := 1 + ∑ j : Fin N, C j
  let d₀ : ℕ := ∑ j : Fin N, d j
  have hsum : 0 ≤ ∑ j : Fin N, C j := Finset.sum_nonneg fun j _ => (hC j).le
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; linarith only [hsum]
  refine ⟨C₀, hC₀, d₀, ?_⟩
  intro V F hV hF hpositive hsurj M hM q hq G hslope hraw k hk hkN
  let j : Fin N := ⟨k - 1, by omega⟩
  have horder : j.val + 1 = k := Nat.sub_add_cancel hk
  have hjet := hb j hV hF hpositive hsurj hM q hq hslope
    (fun s hs hsN => hraw s hs (by omega))
  rw [horder] at hjet
  have hCC : C j ≤ C₀ :=
    (Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdd : d j ≤ d₀ :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) (Finset.mem_univ j)
  exact hjet.trans (mul_le_mul hCC (pow_le_pow_right₀ hM hdd)
    (pow_nonneg (zero_le_one.trans hM) _) hC₀.le)

/-- Polynomial envelopes in one component weight pass from the forward
kernel and its scalar slope denominator to every positive actual inverse
jet.  The source sets may encode a bounded radial strip; only their
inclusion in the coefficient domain is used here. -/
theorem n04PositiveGeometry_scalarInverse_polynomial_bound
    {ι : Type*} (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (V : ι → Set P) (hV : ∀ i, IsOpen (V i))
    (F : ι → P × ℝ → ℝ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (V i ×ˢ univ))
    (hpositive : ∀ i a, a ∈ V i → ∀ r, 0 < deriv (fun t => F i (a, t)) r)
    (hsurj : ∀ i a, a ∈ V i → Function.Surjective (fun t => F i (a, t)))
    (Ω : ι → Set (P × ℝ)) (hΩ : ∀ i, Ω i ⊆ V i ×ˢ univ)
    (hslope : ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧ ∀ i q, q ∈ Ω i →
      |(deriv (fun t => F i (q.1, t))
        (Function.invFun (fun t => F i (q.1, t)) q.2))⁻¹| ≤ A * W i ^ Q)
    (hraw : ∀ k : ℕ, 1 ≤ k → ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧
      ∀ i q, q ∈ Ω i →
        ‖iteratedFDeriv ℝ k (F i)
          (q.1, Function.invFun (fun t => F i (q.1, t)) q.2)‖ ≤ A * W i ^ Q)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ C Q : ℝ, 0 < C ∧ 0 ≤ Q ∧ ∀ i q, q ∈ Ω i →
      ‖iteratedFDeriv ℝ n
        (fun z : P × ℝ => Function.invFun (fun t => F i (z.1, t)) z.2) q‖ ≤
          C * W i ^ Q := by
  let G : ι → P × ℝ → ℝ :=
    fun i q => Function.invFun (fun t => F i (q.1, t)) q.2
  let u : ℕ → ι → P × ℝ → ℝ := fun k i q =>
    if k = 0 then |(deriv (fun t => F i (q.1, t)) (G i q))⁻¹|
    else ‖iteratedFDeriv ℝ k (F i) (q.1, G i q)‖
  have hu (k : ℕ) (_hk : k ≤ n) : ∃ A Q : ℝ, 0 ≤ A ∧ 0 ≤ Q ∧
      ∀ i q, q ∈ Ω i → u k i q ≤ A * W i ^ Q := by
    by_cases hk0 : k = 0
    · simpa only [u, if_pos hk0, G] using hslope
    · simpa only [u, if_neg hk0, G] using hraw k (by omega)
  obtain ⟨A, Q, hA, hQ, hb⟩ := finite_polynomial_majorant W hW Ω u n hu
  obtain ⟨C, hC, d, henv⟩ := n04PositiveGeometry_scalarInverse_jet_envelope (P := P) (n - 1)
  refine ⟨C * (1 + A) ^ d, Q * d,
    mul_pos hC (pow_pos (by linarith only [hA]) d),
    mul_nonneg hQ (Nat.cast_nonneg d), ?_⟩
  intro i q hq
  let M : ℝ := (1 + A) * W i ^ Q
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (by linarith only [hA]) (Real.one_le_rpow (hW i) hQ)
  have hAM : A * W i ^ Q ≤ M :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (zero_le_one.trans (hW i)) Q)
  have hdenom : |(deriv (fun t => F i (q.1, t)) (G i q))⁻¹| ≤ M := by
    have hh := (hb 0 (Nat.zero_le _) i q hq).trans hAM
    simpa only [u, if_pos rfl] using hh
  have hforward (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n - 1 + 1) :
      ‖iteratedFDeriv ℝ k (F i) (q.1, G i q)‖ ≤ M := by
    have hkn' : k ≤ n := by omega
    have hh := (hb k hkn' i q hq).trans hAM
    simpa only [u, if_neg (by omega : k ≠ 0)] using hh
  have hjet := henv (hV i) (hF i) (hpositive i) (hsurj i)
    hM q (hΩ i hq) hdenom hforward
  have horder : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [horder] at hjet
  apply hjet.trans_eq
  change C * ((1 + A) * W i ^ Q) ^ d = _
  rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hW i)) Q d]
  ring

end ActualInverseEnvelope

section OriginalParameterEstimate

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

/-- The actual state inverse tower is bounded by the partition products
of its forward coefficient tower, with a universal scalar kernel factor.
This retains the factors needed for the original one-high interpolation
estimate; no product is replaced by a power of the high state seminorm. -/
theorem n04PositiveGeometry_finiteCoefficient_inverseDirections_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ {U : Set E} {V : Set P} {F : P × ℝ → ℝ} {a : E → P × ℝ},
      ∀ J : SmoothDirections U a,
      ∀ (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F (V ×ˢ univ))
        (hpositive : ∀ c ∈ V, ∀ r, 0 < deriv (fun t => F (c, t)) r)
        (hsurj : ∀ c ∈ V, Function.Surjective (fun t => F (c, t)))
        (hmap : MapsTo a U (V ×ˢ univ)),
      ∀ {M : ℝ}, 1 ≤ M → ∀ x ∈ U,
        let G := fun z : P × ℝ => Function.invFun (fun t => F (z.1, t)) z.2
        |(deriv (fun t => F ((a x).1, t)) (G (a x)))⁻¹| ≤ M →
        (∀ k : ℕ, 1 ≤ k → k ≤ n →
          ‖iteratedFDeriv ℝ k F ((a x).1, G (a x))‖ ≤ M) →
        1 ≤ n → ∀ v : Fin n → E,
          |(n04PositiveGeometry_finiteCoefficient_inverseDirections
            J hV hF hpositive hsurj hmap).D n x v| ≤
            (C * M ^ d) * ∑ c : OrderedFinpartition n,
              ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ := by
  classical
  obtain ⟨C, hC, d, hb⟩ := n04PositiveGeometry_scalarInverse_jet_prefix_envelope (P := P) n
  refine ⟨C, hC, d, ?_⟩
  intro U V F a J hV hF hpositive hsurj hmap M hM x hx G hslope hraw hn v
  have houter := hb hV hF hpositive hsurj hM (a x) (hmap hx) hslope hraw
  rw [n04PositiveGeometry_finiteCoefficient_inverseDirections_apply,
    ← Real.norm_eq_abs, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  have hlength : 1 ≤ c.length := c.length_pos (by omega)
  have hlen : c.length ≤ n := c.length_le
  exact ((iteratedFDeriv ℝ c.length G (a x)).le_opNorm
    (fun i => J.D (c.partSize i) x (v ∘ c.emb i))).trans
    (mul_le_mul_of_nonneg_right (houter c.length hlength hlen)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end OriginalParameterEstimate

end ContinuousFlexibility.Analysis
