import ContinuousFlexibility.Analysis.N06CanonicalCosineCutoff
import ContinuousFlexibility.Analysis.N06WeakFiniteGraph

/-!
# Exact tail identities for the same cosine coefficients and graph fields

One family of radial representatives is used for every finite cutoff.
Removing a smaller finite index set is exactly subtraction of the actual
finite syntheses, of their angular jets, and of all five graph fields.
These pointwise identities give exact differences of the original L2
classes and of the full finite jet squared norms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_finiteSynthesis_sdiff {ι : Type*} [DecidableEq ι]
    {s t : Finset ι} (hst : s ⊆ t) (u e : ι → ℝ → ℝ) :
    r11bFiniteSynthesis (t \ s) u e =
      fun p => r11bFiniteSynthesis t u e p - r11bFiniteSynthesis s u e p := by
  funext p
  exact Finset.sum_sdiff_eq_sub (f := fun i => u i p.1 * e i p.2) hst

/-- Radial regularity is unnecessary: only the smooth angular factors are
differentiated in this identity. -/
theorem n06_mixedAngularDerivative_finiteSynthesis_sdiff
    {ι : Type*} [DecidableEq ι] {s t : Finset ι} (hst : s ⊆ t)
    (u e : ι → ℝ → ℝ) (he : ∀ i ∈ t, ContDiff ℝ ∞ (e i)) (k : ℕ) :
    mixedDerivative 0 k (r11bFiniteSynthesis (t \ s) u e) =
      fun p => mixedDerivative 0 k (r11bFiniteSynthesis t u e) p -
        mixedDerivative 0 k (r11bFiniteSynthesis s u e) p := by
  rw [n06_mixedAngularDerivative_finiteSynthesis (t \ s) u e
    (fun i hi => he i (Finset.mem_sdiff.mp hi).1) k,
    n06_mixedAngularDerivative_finiteSynthesis t u e he k,
    n06_mixedAngularDerivative_finiteSynthesis s u e (fun i hi => he i (hst hi)) k]
  exact n06_finiteSynthesis_sdiff hst u (fun i => iteratedDeriv k (e i))

/-- All five fields use the same globally chosen mode representatives. -/
theorem n06_weakFiniteGraphFields_sdiff {s t : Finset ℕ} (hst : s ⊆ t)
    (v : ℕ → ℝ → ℝ) (k : ℕ) (r : Fin 5) :
    n06WeakFiniteGraphFields (t \ s) v k r =
      fun p => n06WeakFiniteGraphFields t v k r p -
        n06WeakFiniteGraphFields s v k r p :=
  n06_finiteSynthesis_sdiff hst (n06WeakFiniteGraphCoefficients v r)
    (fun i => iteratedDeriv (k + n06WeakFiniteGraphShift r) (referenceAngularBasis i))

/-- The representative identity gives the exact difference of L2 elements,
independently of the proofs used for their membership. -/
theorem n06_toLp_eq_sub_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (heq : f =ᵐ[μ] (fun x => g x - h x)) :
    hf.toLp f = hg.toLp g - hh.toLp h := by
  calc
    _ = (hg.sub hh).toLp (g - h) := hf.toLp_congr (hg.sub hh) heq
    _ = _ := MemLp.toLp_sub hg hh

theorem n06_weakFiniteGraphFields_sdiff_toLp
    {μ : Measure PolarPoint} {s t : Finset ℕ} (hst : s ⊆ t)
    (v : ℕ → ℝ → ℝ) (k : ℕ) (r : Fin 5)
    (hT : MemLp (n06WeakFiniteGraphFields (t \ s) v k r) 2 μ)
    (ht : MemLp (n06WeakFiniteGraphFields t v k r) 2 μ)
    (hs : MemLp (n06WeakFiniteGraphFields s v k r) 2 μ) :
    hT.toLp (n06WeakFiniteGraphFields (t \ s) v k r) =
      ht.toLp (n06WeakFiniteGraphFields t v k r) -
        hs.toLp (n06WeakFiniteGraphFields s v k r) :=
  n06_toLp_eq_sub_of_ae hT ht hs (Eventually.of_forall fun p =>
    congrFun (n06_weakFiniteGraphFields_sdiff hst v k r) p)

theorem n06_cosineCut_tail_angularJet {N M : ℕ} (hNM : N ≤ M)
    (U : PolarPoint → ℝ) (k : ℕ) :
    mixedDerivative 0 k
      (r11bFiniteSynthesis (Finset.range (M + 1) \ Finset.range (N + 1))
        (n06HalfCosineCoefficient U) referenceAngularBasis) =
      fun p => mixedDerivative 0 k (n06CylinderCosineCut M U) p -
        mixedDerivative 0 k (n06CylinderCosineCut N U) p :=
  n06_mixedAngularDerivative_finiteSynthesis_sdiff
    (Finset.range_mono (Nat.add_le_add_right hNM 1))
      (n06HalfCosineCoefficient U) referenceAngularBasis
      (fun i _ => contDiff_referenceAngularBasis i) k

theorem n06_cosineCut_tail_angularJet_memLp
    {μ : Measure PolarPoint} {N M : ℕ} (hNM : N ≤ M)
    (U : PolarPoint → ℝ) (k : ℕ)
    (hM : MemLp (mixedDerivative 0 k (n06CylinderCosineCut M U)) 2 μ)
    (hN : MemLp (mixedDerivative 0 k (n06CylinderCosineCut N U)) 2 μ) :
    MemLp (mixedDerivative 0 k
      (r11bFiniteSynthesis (Finset.range (M + 1) \ Finset.range (N + 1))
        (n06HalfCosineCoefficient U) referenceAngularBasis)) 2 μ :=
  (memLp_congr_ae (Eventually.of_forall fun p =>
    congrFun (n06_cosineCut_tail_angularJet hNM U k) p)).mpr (hM.sub hN)

theorem n06_cosineCut_tail_angularJet_toLp
    {μ : Measure PolarPoint} {N M : ℕ} (hNM : N ≤ M)
    (U : PolarPoint → ℝ) (k : ℕ)
    (hT : MemLp (mixedDerivative 0 k
      (r11bFiniteSynthesis (Finset.range (M + 1) \ Finset.range (N + 1))
        (n06HalfCosineCoefficient U) referenceAngularBasis)) 2 μ)
    (hM : MemLp (mixedDerivative 0 k (n06CylinderCosineCut M U)) 2 μ)
    (hN : MemLp (mixedDerivative 0 k (n06CylinderCosineCut N U)) 2 μ) :
    hT.toLp (mixedDerivative 0 k
      (r11bFiniteSynthesis (Finset.range (M + 1) \ Finset.range (N + 1))
        (n06HalfCosineCoefficient U) referenceAngularBasis)) =
      hM.toLp (mixedDerivative 0 k (n06CylinderCosineCut M U)) -
        hN.toLp (mixedDerivative 0 k (n06CylinderCosineCut N U)) :=
  n06_toLp_eq_sub_of_ae hT hM hN (Eventually.of_forall fun p =>
    congrFun (n06_cosineCut_tail_angularJet hNM U k) p)

/-- The entire fixed-order tail cost is the exact difference cost of the
two cutoffs in their original L2 measure. -/
theorem n06_cosineCut_tail_jetRow_norm_sq
    {μ : Measure PolarPoint} {N M b : ℕ} (hNM : N ≤ M) (U : PolarPoint → ℝ)
    (hT : ∀ k : Fin (b + 1), MemLp (mixedDerivative 0 k.val
      (r11bFiniteSynthesis (Finset.range (M + 1) \ Finset.range (N + 1))
        (n06HalfCosineCoefficient U) referenceAngularBasis)) 2 μ)
    (hM : ∀ k : Fin (b + 1), MemLp
      (mixedDerivative 0 k.val (n06CylinderCosineCut M U)) 2 μ)
    (hN : ∀ k : Fin (b + 1), MemLp
      (mixedDerivative 0 k.val (n06CylinderCosineCut N U)) 2 μ) :
    (∑ k : Fin (b + 1), ‖(hT k).toLp (mixedDerivative 0 k.val
      (r11bFiniteSynthesis (Finset.range (M + 1) \ Finset.range (N + 1))
        (n06HalfCosineCoefficient U) referenceAngularBasis))‖ ^ 2) =
      ∑ k : Fin (b + 1),
        ‖(hM k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut M U)) -
          (hN k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut N U))‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro k _
  rw [n06_cosineCut_tail_angularJet_toLp hNM U k.val (hT k) (hM k) (hN k)]

/-- Two cutoff errors control their full finite jet difference with the
same original limit row. -/
theorem n06_jetRow_sub_sq_le_errors {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] (x y z : ι → E) :
    (∑ i, ‖x i - y i‖ ^ 2) ≤
      2 * (∑ i, ‖x i - z i‖ ^ 2) + 2 * ∑ i, ‖y i - z i‖ ^ 2 := by
  have hpoint (i : ι) : ‖x i - y i‖ ^ 2 ≤
      2 * ‖x i - z i‖ ^ 2 + 2 * ‖y i - z i‖ ^ 2 := by
    have h := norm_sub_le_norm_sub_add_norm_sub (x i) (z i) (y i)
    rw [norm_sub_rev (z i) (y i)] at h
    have hs := (sq_le_sq₀ (norm_nonneg (x i - y i))
      (add_nonneg (norm_nonneg (x i - z i)) (norm_nonneg (y i - z i)))).mpr h
    nlinarith only [hs, sq_nonneg (‖x i - z i‖ - ‖y i - z i‖)]
  calc
    _ ≤ ∑ i, (2 * ‖x i - z i‖ ^ 2 + 2 * ‖y i - z i‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

end ContinuousFlexibility.Analysis
