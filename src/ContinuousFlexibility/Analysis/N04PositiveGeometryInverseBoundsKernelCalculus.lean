module

public import ContinuousFlexibility.Analysis.N04RealizationEnvelopeDifferential
public import ContinuousFlexibility.Analysis.RootCompositionIntegral
public import ContinuousFlexibility.Analysis.BoundaryTaylorBounds
public import ContinuousFlexibility.Analysis.PolynomialJetOperations
public import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets

/-!
# Ordinary kernel jets through the actual radial integrals

This is the finite dimensional calculus used for the displayed radial
kernel.  Its envelopes are uniform in an arbitrary index, which can
contain the component, coefficient vector, and physical evaluation point.
The integral operation keeps the integration point inside that same
uniform index set; it does not select a bound for each component.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology BigOperators Interval

structure N04PositiveKernelJetBounds {I E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : I → ℝ) (p : I → E) (f : I → E → ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ (f i)
  jets : ∀ n, HasPositiveEnvelope W (fun i => ‖iteratedFDeriv ℝ n (f i) (p i)‖)

namespace N04PositiveKernelJetBounds

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {W : I → ℝ} {p : I → E} {f g : I → E → ℝ}

theorem reindex {J : Type*} (hf : N04PositiveKernelJetBounds W p f) (e : J → I) :
    N04PositiveKernelJetBounds (fun j => W (e j)) (fun j => p (e j))
      (fun j => f (e j)) := by
  refine ⟨fun j => hf.smooth (e j), ?_⟩
  intro n
  obtain ⟨C, A, hC, hA, hb⟩ := hf.jets n
  exact ⟨C, A, hC, hA, fun j => hb (e j)⟩

theorem precompLinear {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (hf : N04PositiveKernelJetBounds W p f) (hW : ∀ i, 1 ≤ W i)
    (L : D →L[ℝ] E) (q : I → D) (hq : ∀ i, L (q i) = p i) :
    N04PositiveKernelJetBounds W q (fun i y => f i (L y)) := by
  refine ⟨fun i => (hf.smooth i).comp L.contDiff, ?_⟩
  intro n
  have hb := (hf.jets n).mul hW (hasPositiveEnvelope_const W hW (‖L‖ ^ n))
    (fun _ => pow_nonneg (norm_nonneg L) n)
  apply hb.mono
  intro i
  have h := norm_iteratedFDeriv_comp_linear_le_at L
    ((hf.smooth i).contDiffAt (x := L (q i))) n
  simpa only [Function.comp_def, hq i] using h

theorem const (hW : ∀ i, 1 ≤ W i) (c : I → ℝ)
    (hc : HasPositiveEnvelope W (fun i => |c i|)) :
    N04PositiveKernelJetBounds W p (fun i _ => c i) := by
  refine ⟨fun _ => contDiff_const, ?_⟩
  intro n
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hc
  | succ n =>
      simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using
        hasPositiveEnvelope_const W hW 0

theorem linear (hW : ∀ i, 1 ≤ W i) (L : E →L[ℝ] ℝ)
    (hp : HasPositiveEnvelope W (fun i => ‖p i‖)) :
    N04PositiveKernelJetBounds W p (fun _ => L) := by
  refine ⟨fun _ => L.contDiff, ?_⟩
  intro n
  cases n with
  | zero =>
      apply ((hasPositiveEnvelope_const W hW ‖L‖).mul hW hp
        (fun _ => norm_nonneg _)).mono
      intro i
      simpa only [norm_iteratedFDeriv_zero] using L.le_opNorm (p i)
  | succ n =>
      exact (hasPositiveEnvelope_const W hW ‖L‖).mono
        (fun i => norm_iteratedFDeriv_linear_of_pos L (n + 1) (by omega) (p i))

theorem add (hf : N04PositiveKernelJetBounds W p f)
    (hg : N04PositiveKernelJetBounds W p g) (hW : ∀ i, 1 ≤ W i) :
    N04PositiveKernelJetBounds W p (fun i y => f i y + g i y) :=
  ⟨fun i => (hf.smooth i).add (hg.smooth i), fun n =>
    n04Realization_envelope_add_jets hW p f g
      (fun i => (hf.smooth i).contDiffAt) (fun i => (hg.smooth i).contDiffAt)
      n (hf.jets n) (hg.jets n)⟩

theorem neg (hf : N04PositiveKernelJetBounds W p f) :
    N04PositiveKernelJetBounds W p (fun i y => -f i y) := by
  refine ⟨fun i => (hf.smooth i).neg, ?_⟩
  intro n
  have he (i : I) : ‖iteratedFDeriv ℝ n (fun y => -f i y) (p i)‖ =
      ‖iteratedFDeriv ℝ n (f i) (p i)‖ := by
    simpa only [Pi.neg_def, norm_neg] using congrArg norm
      (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := n) (f := f i) (x := p i))
  simpa only [he] using hf.jets n

theorem sub (hf : N04PositiveKernelJetBounds W p f)
    (hg : N04PositiveKernelJetBounds W p g) (hW : ∀ i, 1 ≤ W i) :
    N04PositiveKernelJetBounds W p (fun i y => f i y - g i y) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg hW

theorem mul (hf : N04PositiveKernelJetBounds W p f)
    (hg : N04PositiveKernelJetBounds W p g) (hW : ∀ i, 1 ≤ W i) :
    N04PositiveKernelJetBounds W p (fun i y => f i y * g i y) :=
  ⟨fun i => (hf.smooth i).mul (hg.smooth i), fun n =>
    n04Realization_envelope_mul_jets hW p f g
      (fun i => (hf.smooth i).contDiffAt) (fun i => (hg.smooth i).contDiffAt) n
      (fun j _ => hf.jets j) (fun j _ => hg.jets j)⟩

theorem pow (hf : N04PositiveKernelJetBounds W p f)
    (hW : ∀ i, 1 ≤ W i) (k : ℕ) :
    N04PositiveKernelJetBounds W p (fun i y => f i y ^ k) := by
  induction k with
  | zero =>
      simpa only [pow_zero] using const (p := p) hW (fun _ => 1)
        (by simpa only [abs_one] using hasPositiveEnvelope_const W hW 1)
  | succ k ih => simpa only [pow_succ] using ih.mul hf hW

theorem sum {J : Type*} (hW : ∀ i, 1 ≤ W i) (s : Finset J)
    (F : J → I → E → ℝ)
    (hF : ∀ j ∈ s, N04PositiveKernelJetBounds W p (F j)) :
    N04PositiveKernelJetBounds W p (fun i y => ∑ j ∈ s, F j i y) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sum_empty] using const (p := p) hW (fun _ => 0)
        (by simpa only [abs_zero] using hasPositiveEnvelope_const W hW 0)
  | @insert j s hj ih =>
      intro hF
      have h := (hF j (Finset.mem_insert_self _ _)).add
        (ih (fun k hk => hF k (Finset.mem_insert_of_mem hk))) hW
      simpa only [Finset.sum_insert hj] using h

/-- A fixed compactly supported smooth cutoff has globally bounded
ordinary jets, so composition only pays for its actual inner scalar jets. -/
theorem cutoff (hf : N04PositiveKernelJetBounds W p f) (hW : ∀ i, 1 ≤ W i) :
    N04PositiveKernelJetBounds W p
      (fun i y => boundaryTaylorCutoff (f i y)) := by
  refine ⟨fun i => boundaryTaylorCutoff.contDiff.comp (hf.smooth i), ?_⟩
  intro n
  apply n04Realization_envelope_comp_jets hW p (fun _ => boundaryTaylorCutoff) f
    (fun _ => boundaryTaylorCutoff.contDiff.contDiffAt)
    (fun i => (hf.smooth i).contDiffAt) n
  · intro j _
    obtain ⟨C, _hC, hb⟩ := exists_boundaryTaylorBasis_jet_bound 0 j
    apply (hasPositiveEnvelope_const W hW C).mono
    intro i
    have he : boundaryTaylorBasis 0 = (boundaryTaylorCutoff : ℝ → ℝ) := by
      funext t
      simp only [boundaryTaylorBasis, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, mul_one]
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, he] using
      hb 0 (Nat.zero_le _) (f i (p i))
  · exact fun j _ _ => hf.jets j

theorem congr (hf : N04PositiveKernelJetBounds W p f)
    (heq : ∀ i, f i = g i) : N04PositiveKernelJetBounds W p g := by
  have he : f = g := funext heq
  exact he ▸ hf

end N04PositiveKernelJetBounds

/-- Fixed interval integration preserves the same component polynomial
envelopes.  The interval length is the only extra scalar factor. -/
theorem n04PositiveGeometry_kernel_intervalIntegral_bounds
    {I E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {W : I → ℝ} (hW : ∀ i, 1 ≤ W i) (p : I → E) (a b : I → ℝ)
    (F : I → E × ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hlength : HasPositiveEnvelope W (fun i => |b i - a i|))
    (hjets : N04PositiveKernelJetBounds
      (fun z : {z : I × ℝ // z.2 ∈ uIcc (a z.1) (b z.1)} => W z.1.1)
      (fun z => (p z.1.1, z.1.2)) (fun z => F z.1.1)) :
    N04PositiveKernelJetBounds W p
      (fun i y => ∫ t in a i..b i, F i (y, t)) := by
  refine ⟨fun i => contDiff_intervalIntegral_of_contDiff (hF i) (a i) (b i), ?_⟩
  intro n
  obtain ⟨C, A, hC, hA, hb⟩ := hjets.jets n
  obtain ⟨D, B, hD, hB, hlength⟩ := hlength
  refine ⟨C * D, A + B, mul_pos hC hD, add_pos hA hB, ?_⟩
  intro i
  have hi := norm_iteratedFDeriv_intervalIntegral_le (hF i) n (a i) (b i) (p i)
    (C * W i ^ A) (fun t ht => hb ⟨(i, t), ht⟩)
  calc
    _ ≤ (C * W i ^ A) * |b i - a i| := hi
    _ ≤ (C * W i ^ A) * (D * W i ^ B) :=
      mul_le_mul_of_nonneg_left (hlength i)
        (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans (hW i)) _))
    _ = (C * D) * W i ^ (A + B) := by
      rw [Real.rpow_add (zero_lt_one.trans_le (hW i))]
      ring

end ContinuousFlexibility.Analysis
