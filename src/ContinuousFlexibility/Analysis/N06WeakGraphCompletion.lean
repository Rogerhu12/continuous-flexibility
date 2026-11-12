import ContinuousFlexibility.Analysis.N06WeakGlobalModes
import ContinuousFlexibility.Analysis.N06CosineCutoffTails
import ContinuousFlexibility.Analysis.N06GraphCauchy

/-!
# Completion of the five weak graph fields in the original canonical L2

All finite tails use one family of H2 radial representatives. Their graph
norm is controlled by the corresponding tails of the original source and
solution jet rows. The actual cosine convergence theorem then gives five
L2 limits at every fixed angular order, with the same graph constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Summing the proved modal estimate over the finite angular jet row. -/
theorem n06_weak_graph_finite_row_bound {b : ℕ} (s : Finset ℕ)
    (u F v : ℕ → ℝ → ℝ) (C : ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hF : ∀ i ∈ s, MemLp (F i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₀ : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2
      (volume.restrict (Ioo (0 : ℝ) 1)))
    (hmode : ∀ i ∈ s, n06WeakModeGraphSquare (((2 * i : ℕ) : ℝ)) (v i) ≤
      C * ((∫ y in (0 : ℝ)..1, F i y ^ 2) + ∫ y in (0 : ℝ)..1, u i y ^ 2))
    (hU : ∀ k : Fin (b + 1), MemLp (mixedDerivative 0 k.val
      (r11bFiniteSynthesis s u referenceAngularBasis)) 2 (cylinderWindowMeasure 0))
    (hFs : ∀ k : Fin (b + 1), MemLp (mixedDerivative 0 k.val
      (r11bFiniteSynthesis s F referenceAngularBasis)) 2 (cylinderWindowMeasure 0))
    (hg : ∀ k : Fin (b + 1), ∀ r : Fin 5,
      MemLp (n06WeakFiniteGraphFields s v k.val r) 2 (cylinderWindowMeasure 0)) :
    (∑ k : Fin (b + 1), ∑ r : Fin 5,
      ‖(hg k r).toLp (n06WeakFiniteGraphFields s v k.val r)‖ ^ 2) ≤
      C * ((∑ k : Fin (b + 1), ‖(hFs k).toLp (mixedDerivative 0 k.val
        (r11bFiniteSynthesis s F referenceAngularBasis))‖ ^ 2) +
        ∑ k : Fin (b + 1), ‖(hU k).toLp (mixedDerivative 0 k.val
          (r11bFiniteSynthesis s u referenceAngularBasis))‖ ^ 2) := by
  calc
    _ ≤ ∑ k : Fin (b + 1), C *
        (‖(hFs k).toLp (mixedDerivative 0 k.val
          (r11bFiniteSynthesis s F referenceAngularBasis))‖ ^ 2 +
          ‖(hU k).toLp (mixedDerivative 0 k.val
            (r11bFiniteSynthesis s u referenceAngularBasis))‖ ^ 2) := by
      exact Finset.sum_le_sum (fun k _ =>
        n06_weak_finite_graph_lp_bound_of_modes s u F v C hu hF hv₀ hv₁ hv₂ hmode
          k.val (hU k) (hFs k) (hg k))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- The actual finite graph estimate controls each ordered cutoff tail. -/
theorem n06_weak_graph_cutoff_tail_bound {μ : Measure PolarPoint} {b : ℕ}
    (U F : Fin (b + 1) → Lp ℝ 2 μ) (v : ℕ → ℝ → ℝ) (C : ℝ)
    (hg : ∀ s : Finset ℕ, ∀ k : Fin (b + 1), ∀ r : Fin 5,
      MemLp (n06WeakFiniteGraphFields s v k.val r) 2 μ)
    (hUC : ∀ N : ℕ, ∀ k : Fin (b + 1), MemLp
      (mixedDerivative 0 k.val (n06CylinderCosineCut N (U 0))) 2 μ)
    (hFC : ∀ N : ℕ, ∀ k : Fin (b + 1), MemLp
      (mixedDerivative 0 k.val (n06CylinderCosineCut N (F 0))) 2 μ)
    (hfinite : ∀ (s : Finset ℕ)
      (hUs : ∀ k : Fin (b + 1), MemLp (mixedDerivative 0 k.val
        (r11bFiniteSynthesis s (n06HalfCosineCoefficient (U 0)) referenceAngularBasis)) 2 μ)
      (hFs : ∀ k : Fin (b + 1), MemLp (mixedDerivative 0 k.val
        (r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis)) 2 μ),
      (∑ k : Fin (b + 1), ∑ r : Fin 5,
        ‖(hg s k r).toLp (n06WeakFiniteGraphFields s v k.val r)‖ ^ 2) ≤
        C * ((∑ k : Fin (b + 1), ‖(hFs k).toLp (mixedDerivative 0 k.val
          (r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis))‖ ^ 2) +
          ∑ k : Fin (b + 1), ‖(hUs k).toLp (mixedDerivative 0 k.val
            (r11bFiniteSynthesis s (n06HalfCosineCoefficient (U 0)) referenceAngularBasis))‖ ^ 2))
    (k : Fin (b + 1)) (r : Fin 5) (N M : ℕ) (hNM : N ≤ M) :
    ‖(hg (Finset.range (M + 1)) k r).toLp
        (n06WeakFiniteGraphFields (Finset.range (M + 1)) v k.val r) -
      (hg (Finset.range (N + 1)) k r).toLp
        (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r)‖ ^ 2 ≤
      C * ((∑ j : Fin (b + 1),
        ‖(hFC M j).toLp (mixedDerivative 0 j.val (n06CylinderCosineCut M (F 0))) -
          (hFC N j).toLp (mixedDerivative 0 j.val (n06CylinderCosineCut N (F 0)))‖ ^ 2) +
        ∑ j : Fin (b + 1),
        ‖(hUC M j).toLp (mixedDerivative 0 j.val (n06CylinderCosineCut M (U 0))) -
          (hUC N j).toLp (mixedDerivative 0 j.val (n06CylinderCosineCut N (U 0)))‖ ^ 2) := by
  let s : Finset ℕ := Finset.range (M + 1) \ Finset.range (N + 1)
  have hsubset : Finset.range (N + 1) ⊆ Finset.range (M + 1) :=
    Finset.range_mono (Nat.add_le_add_right hNM 1)
  let hUs (j : Fin (b + 1)) :=
    n06_cosineCut_tail_angularJet_memLp hNM (U 0) j.val (hUC M j) (hUC N j)
  let hFs (j : Fin (b + 1)) :=
    n06_cosineCut_tail_angularJet_memLp hNM (F 0) j.val (hFC M j) (hFC N j)
  have hsum := hfinite s hUs hFs
  have heq := n06_weakFiniteGraphFields_sdiff_toLp hsubset v k.val r (hg s k r)
    (hg (Finset.range (M + 1)) k r) (hg (Finset.range (N + 1)) k r)
  rw [← heq]
  have hsingle : ‖(hg s k r).toLp (n06WeakFiniteGraphFields s v k.val r)‖ ^ 2 ≤
      ∑ j : Fin (b + 1), ∑ l : Fin 5,
        ‖(hg s j l).toLp (n06WeakFiniteGraphFields s v j.val l)‖ ^ 2 :=
    (Finset.single_le_sum (fun l _ => sq_nonneg
      ‖(hg s k l).toLp (n06WeakFiniteGraphFields s v k.val l)‖)
        (Finset.mem_univ r)).trans
      (Finset.single_le_sum
        (fun j _ => Finset.sum_nonneg (fun l _ => sq_nonneg
          ‖(hg s j l).toLp (n06WeakFiniteGraphFields s v j.val l)‖))
        (Finset.mem_univ k))
  have hFeq := n06_cosineCut_tail_jetRow_norm_sq hNM (F 0) hFs (hFC M) (hFC N)
  have hUeq := n06_cosineCut_tail_jetRow_norm_sq hNM (U 0) hUs (hUC M) (hUC N)
  rw [hFeq, hUeq] at hsum
  exact hsingle.trans hsum

/-- Finite graph rows controlled by convergent source rows have limits with
exactly the same squared norm bound. -/
theorem n06_finite_row_graph_limit {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [CompleteSpace E]
    (X : ℕ → ι → κ → E) (UC FC : ℕ → ι → E) (U F : ι → E)
    {C : ℝ} (hC : 0 ≤ C)
    (hUlim : Tendsto (fun N => ∑ k, ‖UC N k - U k‖ ^ 2) atTop (𝓝 0))
    (hFlim : Tendsto (fun N => ∑ k, ‖FC N k - F k‖ ^ 2) atTop (𝓝 0))
    (hfinite : ∀ N, (∑ k, ∑ r, ‖X N k r‖ ^ 2) ≤
      C * ((∑ k, ‖FC N k‖ ^ 2) + ∑ k, ‖UC N k‖ ^ 2))
    (htail : ∀ k r N M, N ≤ M → ‖X M k r - X N k r‖ ^ 2 ≤
      C * ((∑ j, ‖FC M j - FC N j‖ ^ 2) + ∑ j, ‖UC M j - UC N j‖ ^ 2)) :
    ∃ G : ι → κ → E,
      (∀ k r, Tendsto (fun N => X N k r) atTop (𝓝 (G k r))) ∧
      (∑ k, ∑ r, ‖G k r‖ ^ 2) ≤ C * ((∑ k, ‖F k‖ ^ 2) + ∑ k, ‖U k‖ ^ 2) := by
  let e (N : ℕ) : ℝ := (∑ k, ‖FC N k - F k‖ ^ 2) + ∑ k, ‖UC N k - U k‖ ^ 2
  have he (N : ℕ) : 0 ≤ e N :=
    add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have helim : Tendsto e atTop (𝓝 0) := by
    simpa only [e, add_zero] using hFlim.add hUlim
  have htail' (k : ι) (r : κ) (N M : ℕ) (hNM : N ≤ M) :
      ‖X M k r - X N k r‖ ^ 2 ≤ C * (2 * e N + 2 * e M) := by
    have herrors :
        ((∑ j, ‖FC M j - FC N j‖ ^ 2) + ∑ j, ‖UC M j - UC N j‖ ^ 2) ≤
          2 * e N + 2 * e M := by
      have h₁ := n06_jetRow_sub_sq_le_errors (FC M) (FC N) F
      have h₂ := n06_jetRow_sub_sq_le_errors (UC M) (UC N) U
      dsimp only [e]
      linarith only [h₁, h₂]
    exact (htail k r N M hNM).trans (mul_le_mul_of_nonneg_left herrors hC)
  have hCauchy (k : ι) (r : κ) : CauchySeq (fun N => X N k r) :=
    n06_cauchySeq_of_sq_norm_sub_le_errors _ e hC he helim (htail' k r)
  choose G hG using fun k r => cauchySeq_tendsto_of_complete (hCauchy k r)
  have hleft : Tendsto (fun N => ∑ k, ∑ r, ‖X N k r‖ ^ 2)
      atTop (𝓝 (∑ k, ∑ r, ‖G k r‖ ^ 2)) :=
    tendsto_finsetSum Finset.univ (fun k _ => n06_tendsto_sum_sq_norm (hG k))
  have hUcomp (k : ι) : Tendsto (fun N => UC N k) atTop (𝓝 (U k)) :=
    n06_tendsto_component_of_sum_sq_errors hUlim k
  have hFcomp (k : ι) : Tendsto (fun N => FC N k) atTop (𝓝 (F k)) :=
    n06_tendsto_component_of_sum_sq_errors hFlim k
  have hright := ((n06_tendsto_sum_sq_norm hFcomp).add
    (n06_tendsto_sum_sq_norm hUcomp)).const_mul C
  exact ⟨G, hG, le_of_tendsto_of_tendsto' hleft hright hfinite⟩

/-- Completion of the actual graph cutoffs from their original source-row
convergence. The canonical theorem below supplies that convergence from the
frozen weak angular derivative and reflection conditions. -/
theorem n06_weak_graph_complete_of_cutoff_convergence
    {μ : Measure PolarPoint} (hμ : μ = cylinderWindowMeasure 0) {b : ℕ}
    (U F : Fin (b + 1) → Lp ℝ 2 μ) {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hweak : n06UnitReferenceWeakEquation a c V (U 0) (F 0))
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K)
    (hUC : ∀ N : ℕ, ∀ k : Fin (b + 1), MemLp
      (mixedDerivative 0 k.val (n06CylinderCosineCut N (U 0))) 2 μ)
    (hFC : ∀ N : ℕ, ∀ k : Fin (b + 1), MemLp
      (mixedDerivative 0 k.val (n06CylinderCosineCut N (F 0))) 2 μ)
    (hUlim : Tendsto (fun N => ∑ k : Fin (b + 1),
      ‖(hUC N k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut N (U 0))) - U k‖ ^ 2)
      atTop (𝓝 0))
    (hFlim : Tendsto (fun N => ∑ k : Fin (b + 1),
      ‖(hFC N k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut N (F 0))) - F k‖ ^ 2)
      atTop (𝓝 0)) :
    ∃ v : ℕ → ℝ → ℝ,
      (∀ i, N06WeakModeRepresentative a c V
        (n06HalfCosineCoefficient (U 0) i) (n06HalfCosineCoefficient (F 0) i) (v i)
          (((2 * i : ℕ) : ℝ))) ∧
      ∃ hgraph : ∀ N : ℕ, ∀ k : Fin (b + 1), ∀ r : Fin 5, MemLp
        (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r) 2 μ,
      ∃ G : Fin (b + 1) → Fin 5 → Lp ℝ 2 μ,
        (∀ k r, Tendsto (fun N => (hgraph N k r).toLp
          (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r)) atTop (𝓝 (G k r))) ∧
        (∑ k : Fin (b + 1), ∑ r : Fin 5, ‖G k r‖ ^ 2) ≤
          16384 * K ^ 10 *
            ((∑ k : Fin (b + 1), ‖F k‖ ^ 2) + ∑ k : Fin (b + 1), ‖U k‖ ^ 2) := by
  subst μ
  obtain ⟨v, hv, hmode⟩ := n06_unit_weakPDE_all_modes ha hc hV hq
    (Lp.memLp (U 0)) (Lp.memLp (F 0)) hweak hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  let C : ℝ := 16384 * K ^ 10
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (pow_nonneg (by linarith) 10)
  let hg (s : Finset ℕ) (k : Fin (b + 1)) (r : Fin 5) :
      MemLp (n06WeakFiniteGraphFields s v k.val r) 2 (cylinderWindowMeasure 0) :=
    n06_weak_finiteGraphFields_memLp s v (fun i _ => (hv i).memLp)
      (fun i _ => (hv i).firstMemLp) (fun i _ => (hv i).secondMemLp) k.val r
  have hfinite (s : Finset ℕ)
      (hUs : ∀ k : Fin (b + 1), MemLp (mixedDerivative 0 k.val
        (r11bFiniteSynthesis s (n06HalfCosineCoefficient (U 0)) referenceAngularBasis)) 2
          (cylinderWindowMeasure 0))
      (hFs : ∀ k : Fin (b + 1), MemLp (mixedDerivative 0 k.val
        (r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis)) 2
          (cylinderWindowMeasure 0)) :=
    n06_weak_graph_finite_row_bound s
      (n06HalfCosineCoefficient (U 0)) (n06HalfCosineCoefficient (F 0)) v C
      (fun i _ => n06_halfCosineCoefficient_memLp (Lp.memLp (U 0)) i)
      (fun i _ => n06_halfCosineCoefficient_memLp (Lp.memLp (F 0)) i)
      (fun i _ => (hv i).memLp) (fun i _ => (hv i).firstMemLp)
      (fun i _ => (hv i).secondMemLp) (fun i _ => hmode i) hUs hFs (hg s)
  let X (N : ℕ) (k : Fin (b + 1)) (r : Fin 5) : Lp ℝ 2 (cylinderWindowMeasure 0) :=
    (hg (Finset.range (N + 1)) k r).toLp
      (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r)
  let UC (N : ℕ) (k : Fin (b + 1)) : Lp ℝ 2 (cylinderWindowMeasure 0) :=
    (hUC N k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut N (U 0)))
  let FC (N : ℕ) (k : Fin (b + 1)) : Lp ℝ 2 (cylinderWindowMeasure 0) :=
    (hFC N k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut N (F 0)))
  obtain ⟨G, hG, hbound⟩ := n06_finite_row_graph_limit X UC FC U F hC hUlim hFlim
    (fun N => hfinite (Finset.range (N + 1)) (hUC N) (hFC N))
    (n06_weak_graph_cutoff_tail_bound U F v C hg hUC hFC hfinite)
  exact ⟨v, hv, fun N k r => hg (Finset.range (N + 1)) k r, G, hG, hbound⟩

/-- Actual canonical weak jet rows and the actual canonical weak PDE supply
the graph limits in their original L2 space. No cutoff convergence or strong
radial derivative assumption is required from the caller. -/
theorem n06_canonical_unit_weak_graph_complete
    {S : PhysicalSpacesData} {Kc : CanonicalData S} {m b : ℕ}
    (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (U F : Fin (b + 1) → CanonicalL2 S Kc m)
    (hUeven : (fun p : PolarPoint => U 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (U 0 : PolarPoint → ℝ))
    (hFeven : (fun p : PolarPoint => F 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (F 0 : PolarPoint → ℝ))
    (hUjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (U 0) (U k) k.val)
    (hFjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (F 0) (F k) k.val)
    {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hweak : ∀ φ, CanonicalTest S Kc m φ →
      (∫ p, U 0 p * n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S Kc m) =
        ∫ p, F 0 p * φ p ∂canonicalMeasure S Kc m)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    ∃ v : ℕ → ℝ → ℝ,
      (∀ i, N06WeakModeRepresentative a c V
        (n06HalfCosineCoefficient (U 0) i) (n06HalfCosineCoefficient (F 0) i) (v i)
          (((2 * i : ℕ) : ℝ))) ∧
      ∃ hgraph : ∀ N : ℕ, ∀ k : Fin (b + 1), ∀ r : Fin 5, MemLp
        (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r) 2 (canonicalMeasure S Kc m),
      ∃ G : Fin (b + 1) → Fin 5 → CanonicalL2 S Kc m,
        (∀ k r, Tendsto (fun N => (hgraph N k r).toLp
          (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r)) atTop (𝓝 (G k r))) ∧
        (∑ k : Fin (b + 1), ∑ r : Fin 5, ‖G k r‖ ^ 2) ≤
          16384 * K ^ 10 *
            ((∑ k : Fin (b + 1), ‖F k‖ ^ 2) + ∑ k : Fin (b + 1), ‖U k‖ ^ 2) := by
  obtain ⟨hUC, hUlim⟩ := n06_canonicalCosineCut_jetRow_tendsto U hUeven hUjets
  obtain ⟨hFC, hFlim⟩ := n06_canonicalCosineCut_jetRow_tendsto F hFeven hFjets
  exact n06_weak_graph_complete_of_cutoff_convergence
    (n06_canonical_unit_measure_eq_window hl hr) U F ha hc hV hq
    (n06_canonical_unit_weakEquation hl hr (U 0) (F 0) hweak)
    hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂ hUC hFC hUlim hFlim

end ContinuousFlexibility.Analysis
