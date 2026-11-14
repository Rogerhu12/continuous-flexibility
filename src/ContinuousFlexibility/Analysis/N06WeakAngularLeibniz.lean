module

public import ContinuousFlexibility.Analysis.N06WeakAngularCalculus
public import ContinuousFlexibility.Analysis.CylinderMixedJets
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite Leibniz jets of genuinely weak canonical fields

The coefficient is smooth only on the open canonical strip. The source
jets are arbitrary elements of the actual canonical L² space. Applying
the first weak product rule to each triangular entry and Pascal's identity
proves every finite Leibniz row without differentiating an L² representative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- Integration against a continuous test is linear on the actual L² space. -/
def n06CanonicalPairing (φ : PolarPoint → ℝ) (hφ : Continuous φ) :
    CanonicalL2 S K m →ₗ[ℝ] ℝ where
  toFun f := ∫ p, f p * φ p ∂canonicalMeasure S K m
  map_add' f g := by
    calc
      _ = ∫ p, (f p * φ p + g p * φ p) ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with p hp
        rw [hp]
        simp only [Pi.add_apply, add_mul]
      _ = _ := integral_add
        (n06_integrable_canonical_mul_continuous f hφ)
        (n06_integrable_canonical_mul_continuous g hφ)
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    calc
      _ = ∫ p, c * (f p * φ p) ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with p hp
        rw [hp]
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      _ = _ := integral_const_mul _ _

theorem WeakCanonicalAngularDerivative.n06_zero (j : ℕ) :
    WeakCanonicalAngularDerivative S K m 0 0 j := by
  intro φ hφ
  change n06CanonicalPairing φ hφ.1.continuous 0 =
    (-1 : ℝ) ^ j * n06CanonicalPairing (mixedDerivative 0 j φ)
      (contDiff_mixedDerivative hφ.1 0 j).continuous 0
  simp only [map_zero, mul_zero]

theorem WeakCanonicalAngularDerivative.n06_self (f : CanonicalL2 S K m) :
    WeakCanonicalAngularDerivative S K m f f 0 := by
  intro φ _
  simp only [pow_zero, one_mul, spaces_mixedDerivative_zero]

theorem WeakCanonicalAngularDerivative.n06_smul
    {f g : CanonicalL2 S K m} {j : ℕ}
    (h : WeakCanonicalAngularDerivative S K m f g j) (c : ℝ) :
    WeakCanonicalAngularDerivative S K m (c • f) (c • g) j := by
  intro φ hφ
  change n06CanonicalPairing φ hφ.1.continuous (c • g) =
    (-1 : ℝ) ^ j * n06CanonicalPairing (mixedDerivative 0 j φ)
      (contDiff_mixedDerivative hφ.1 0 j).continuous (c • f)
  rw [map_smul, map_smul]
  change c * (∫ p, g p * φ p ∂canonicalMeasure S K m) =
    (-1 : ℝ) ^ j * (c * ∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m)
  rw [h φ hφ]
  ring

theorem WeakCanonicalAngularDerivative.n06_nsmul
    {f g : CanonicalL2 S K m} {j : ℕ}
    (h : WeakCanonicalAngularDerivative S K m f g j) (c : ℕ) :
    WeakCanonicalAngularDerivative S K m (c • f) (c • g) j := by
  simpa only [Nat.cast_smul_eq_nsmul] using h.n06_smul (c : ℝ)

theorem WeakCanonicalAngularDerivative.n06_sum
    {ι : Type*} (I : Finset ι) {f g : ι → CanonicalL2 S K m} {j : ℕ}
    (h : ∀ i ∈ I, WeakCanonicalAngularDerivative S K m (f i) (g i) j) :
    WeakCanonicalAngularDerivative S K m (∑ i ∈ I, f i) (∑ i ∈ I, g i) j := by
  intro φ hφ
  change n06CanonicalPairing φ hφ.1.continuous (∑ i ∈ I, g i) =
    (-1 : ℝ) ^ j * n06CanonicalPairing (mixedDerivative 0 j φ)
      (contDiff_mixedDerivative hφ.1 0 j).continuous (∑ i ∈ I, f i)
  rw [map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi φ hφ)

/-- Pure angular coefficient jets retain the period on the strip. -/
theorem n06_mixedAngular_periodicOn {a : PolarPoint → ℝ}
    (hp : ∀ p ∈ canonicalOpen S K m, a (p + (0, Real.pi)) = a p)
    (i : ℕ) :
    ∀ p ∈ canonicalOpen S K m,
      mixedDerivative 0 i a (p + (0, Real.pi)) = mixedDerivative 0 i a p := by
  intro p hpU
  have he : (fun θ : ℝ => a (p.1, θ + Real.pi)) = fun θ => a (p.1, θ) := by
    funext θ
    simpa only [Prod.mk_add_mk, add_zero] using hp (p.1, θ) ⟨hpU.1, mem_univ θ⟩
  have hd := congrArg (fun f : ℝ → ℝ => iteratedDeriv i f) he
  rw [iteratedDeriv_comp_add_const i (fun θ : ℝ => a (p.1, θ)) Real.pi] at hd
  simpa only [mixedDerivative, iteratedDeriv_zero, Prod.fst_add, Prod.snd_add,
    add_zero] using congrFun hd p.2

/-- The actual angular derivative of each coefficient jet is its next jet
at every interior point; no extension across a radial endpoint is assumed. -/
theorem n06_angularPartial_mixedAngular_on {a : PolarPoint → ℝ}
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (i : ℕ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    angularPartial (mixedDerivative 0 i a) p = mixedDerivative 0 (i + 1) a p := by
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hg := contDiffOn_mixedDerivative hU ha 0 i
  have hd := (hg.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hσ : HasDerivAt (fun θ : ℝ => (p.1, θ)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
  have hs := hd.hasFDerivAt.comp_hasDerivAt p.2 hσ
  simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero,
    iteratedDeriv_succ, angularPartial] using hs.deriv.symm

/-- The k-th binomial row, formed inside the actual L² vector space. -/
def n06WeakLeibnizRow (X : ℕ → ℕ → CanonicalL2 S K m) (k : ℕ) :
    CanonicalL2 S K m :=
  ∑ i ∈ Finset.range (k + 1), k.choose i • X i (k - i)

@[simp] theorem n06WeakLeibnizRow_zero (X : ℕ → ℕ → CanonicalL2 S K m) :
    n06WeakLeibnizRow X 0 = X 0 0 := by
  simp [n06WeakLeibnizRow]

/-- Pascal's identity combines the two first-derivative terms into the
next complete binomial row. -/
theorem n06WeakLeibnizRow_succ (X : ℕ → ℕ → CanonicalL2 S K m) (k : ℕ) :
    n06WeakLeibnizRow X (k + 1) =
      ∑ i ∈ Finset.range (k + 1),
        k.choose i • (X i (k - i + 1) + X (i + 1) (k - i)) := by
  rw [n06WeakLeibnizRow, Finset.sum_choose_succ_nsmul]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [show k + 1 - i = k - i + 1 by omega]

theorem n06WeakLeibnizRow_successive
    {X : ℕ → ℕ → CanonicalL2 S K m} {k : ℕ}
    (hX : ∀ i ∈ Finset.range (k + 1),
      WeakCanonicalAngularDerivative S K m (X i (k - i))
        (X i (k - i + 1) + X (i + 1) (k - i)) 1) :
    WeakCanonicalAngularDerivative S K m
      (n06WeakLeibnizRow X k) (n06WeakLeibnizRow X (k + 1)) 1 := by
  rw [n06WeakLeibnizRow_succ]
  exact WeakCanonicalAngularDerivative.n06_sum (Finset.range (k + 1))
    (fun i hi => (hX i hi).n06_nsmul (k.choose i))

/-- The all-orders weak Leibniz theorem through the prescribed finite
order. Every entry is identified with a genuine coefficient times a
stored weak L² jet; the source is never assumed smooth. -/
theorem n06_weakAngularLeibniz
    {a : PolarPoint → ℝ} (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m))
    (hp : ∀ p ∈ canonicalOpen S K m, a (p + (0, Real.pi)) = a p)
    (f : ℕ → CanonicalL2 S K m) (b : ℕ)
    (hf : ∀ j, j < b → WeakCanonicalAngularDerivative S K m (f j) (f (j + 1)) 1)
    (X : ℕ → ℕ → CanonicalL2 S K m)
    (hX : ∀ i j, i ≤ b →
      (X i j : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => mixedDerivative 0 i a p * f j p) :
    ∀ k, k ≤ b → WeakCanonicalAngularDerivative S K m
      (X 0 0) (n06WeakLeibnizRow X k) k := by
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hstep (k : ℕ) (hk : k < b) :
      WeakCanonicalAngularDerivative S K m
        (n06WeakLeibnizRow X k) (n06WeakLeibnizRow X (k + 1)) 1 := by
    apply n06WeakLeibnizRow_successive
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hib : i ≤ b := le_trans hik hk.le
    have hi1b : i + 1 ≤ b := by omega
    have hjb : k - i < b := lt_of_le_of_lt (Nat.sub_le _ _) hk
    apply n06_weakCanonicalAngularDerivative_mul_of_contDiffOn
      (hf (k - i) hjb) (contDiffOn_mixedDerivative hU ha 0 i)
      (n06_mixedAngular_periodicOn hp i) (hX i (k - i) hib)
    filter_upwards [Lp.coeFn_add (X i (k - i + 1)) (X (i + 1) (k - i)),
      hX i (k - i + 1) hib, hX (i + 1) (k - i) hi1b,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hsum hleft hright hpU
    rw [hsum]
    simp only [Pi.add_apply]
    rw [hleft, hright, n06_angularPartial_mixedAngular_on ha i ⟨hpU.1, mem_univ p.2⟩]
  intro k
  induction k with
  | zero =>
    intro _
    simpa only [n06WeakLeibnizRow_zero] using
      WeakCanonicalAngularDerivative.n06_self (X 0 0)
  | succ k ih =>
    intro hk
    exact (ih (by omega)).n06_trans (hstep k (by omega))

/-- The L² row has exactly the usual pointwise binomial representative. -/
theorem n06WeakLeibnizRow_ae
    {a : PolarPoint → ℝ} (f : ℕ → CanonicalL2 S K m)
    (X : ℕ → ℕ → CanonicalL2 S K m) (k : ℕ)
    (hX : ∀ i ∈ Finset.range (k + 1),
      (X i (k - i) : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => mixedDerivative 0 i a p * f (k - i) p) :
    (n06WeakLeibnizRow X k : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * mixedDerivative 0 i a p * f (k - i) p := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      ((k.choose i • X i (k - i) : CanonicalL2 S K m) : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          fun p => (k.choose i : ℝ) * mixedDerivative 0 i a p * f (k - i) p := by
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    filter_upwards [Lp.coeFn_smul (k.choose i : ℝ) (X i (k - i)), hX i hi] with p hs hx
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx, mul_assoc]
  have hsum := eventuallyEq_sum hterm
  have hsum' : (fun p => ∑ i ∈ Finset.range (k + 1),
      (k.choose i • X i (k - i) : CanonicalL2 S K m) p) =ᵐ[canonicalMeasure S K m]
      fun p => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * mixedDerivative 0 i a p * f (k - i) p := by
    filter_upwards [hsum] with p hp
    simpa only [Finset.sum_apply] using hp
  exact (Lp.coeFn_fun_finsetSum (Finset.range (k + 1))
    (fun i => k.choose i • X i (k - i))).trans hsum'

end ContinuousFlexibility.Statements
