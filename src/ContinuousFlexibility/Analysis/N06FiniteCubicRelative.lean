import ContinuousFlexibility.Analysis.N06CubicJetBounds

/-!
# The actual finite-mode cubic perturbation relative to the reference graph

The same finite even Fourier solution and its radial forcing enter both
the reference graph estimate and the genuine perturbed divergence. Their
composition gives a fixed-order L² bound independent of the Fourier cutoff.
All five weighted derivative fields and all their memberships are derived
from the radial equations, rather than supplied as an operator estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- A genuine cubic principal-part difference is relatively bounded on
finite even Fourier solutions of the reference radial equations, at every
fixed angular order. The coefficient smallness is on ordinary spatial jets
through b + 1, while the solution and forcing use only angular jets through b. -/
theorem n06_finite_even_cubic_relative_bound
    (s : Finset ℕ) (u F : ℕ → ℝ → ℝ) (b : ℕ)
    {a c V q : ℝ → ℝ} {K δ : ℝ} {A B C : PolarPoint → ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hF : ∀ i ∈ s, ∀ y, F i y =
      -deriv (fun t => a t * deriv (u i) t) y +
        ((2 * i : ℕ) : ℝ) ^ 2 * c y * u i y + V y * u i y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (hδ : 0 ≤ δ)
    (hcoeff : ∀ᵐ p ∂cylinderWindowMeasure 0, ∀ j k : ℕ, j + k ≤ b + 1 →
      |mixedDerivative j k A p| ≤ δ ∧ |mixedDerivative j k B p| ≤ δ ∧
        |mixedDerivative j k C p| ≤ δ) :
    let U := r11bFiniteSynthesis s u referenceAngularBasis
    let G := r11bFiniteSynthesis s F referenceAngularBasis
    let P := divergenceOperator
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C) U
    ∃ hULp : ∀ k : ℕ, MemLp (mixedDerivative 0 k U) 2 (cylinderWindowMeasure 0),
    ∃ hGLp : ∀ k : ℕ, MemLp (mixedDerivative 0 k G) 2 (cylinderWindowMeasure 0),
    ∃ hPLp : ∀ k : Fin (b + 1),
        MemLp (mixedDerivative 0 k.val P) 2 (cylinderWindowMeasure 0),
      (∑ k : Fin (b + 1), ‖(hPLp k).toLp (mixedDerivative 0 k.val P)‖ ^ 2) ≤
        (2048000 * n06AngularMultiplierCost b * K ^ 10 * δ ^ 2) *
          ((∑ k : Fin (b + 1), ‖(hGLp k.val).toLp (mixedDerivative 0 k.val G)‖ ^ 2) +
            ∑ k : Fin (b + 1), ‖(hULp k.val).toLp (mixedDerivative 0 k.val U)‖ ^ 2) := by
  let U := r11bFiniteSynthesis s u referenceAngularBasis
  let G := r11bFiniteSynthesis s F referenceAngularBasis
  have hU : ContDiff ℝ ∞ U := n06_contDiff_finiteSynthesis s u referenceAngularBasis hu
    (fun i _ => contDiff_referenceAngularBasis i)
  have hFc (i : ℕ) (hi : i ∈ s) : Continuous (F i) :=
    continuous_forcing ha ((hu i hi).of_le (by simp)) hc hV (hF i hi)
  have hGjet (k : ℕ) : Continuous (mixedDerivative 0 k G) :=
    n06_continuous_angularJet_finiteSynthesis s F referenceAngularBasis hFc
      (fun i _ => contDiff_referenceAngularBasis i) k
  have hper (v : ℕ → ℝ → ℝ) :
      Function.Periodic (r11bFiniteSynthesis s v referenceAngularBasis) (0, Real.pi) := by
    intro p
    apply Finset.sum_congr rfl
    intro i _
    simp only [Prod.fst_add, Prod.snd_add, add_zero, referenceAngularBasis_periodic i p.2]
  let hULp (k : ℕ) : MemLp (mixedDerivative 0 k U) 2 (cylinderWindowMeasure 0) :=
    continuous_memLp_cylinderWindow (contDiff_mixedDerivative hU 0 k).continuous 0
  let hGLp (k : ℕ) : MemLp (mixedDerivative 0 k G) 2 (cylinderWindowMeasure 0) :=
    continuous_memLp_cylinderWindow (hGjet k) 0
  let hgraph (k : ℕ) (i : Fin 5) :
      MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1)
        (mixedDerivative 0 k U) i) 2 (cylinderWindowMeasure 0) :=
    n06_cubicGraphFields_angularJet_memLp hU k i
  have heorth (i j : ℕ) :
      angularPairing (referenceAngularBasis i) (referenceAngularBasis j) =
        if i = j then 1 else 0 := by
    simpa only [angularPairing, angularAverage, radialAngularMean, one_div] using
      referenceAngularBasis_pairing i j
  have hgraphBound : n06CylinderGraphJetSquare b U ≤
      16384 * K ^ 10 * (n06CylinderJetSquare b G + n06CylinderJetSquare b U) :=
    n06_finite_cylinder_graph_jet_bound s u F referenceAngularBasis n06AngularPartner
      (fun i => ((2 * i : ℕ) : ℝ)) b ha hu hc hV hq hF
      (fun i _ => contDiff_referenceAngularBasis i)
      (fun i _ => n06_contDiff_angularPartner i)
      (fun i _ j _ => heorth i j)
      (fun i _ j _ => n06_angularPartner_pairing i j)
      (fun i _ θ => n06_referenceAngularBasis_hasDerivAt i θ)
      (fun i _ θ => n06_angularPartner_hasDerivAt i θ)
      hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  have hgraphLp := n06_cubicGraphFields_angularJet_lp_bound hU (hper u) (hper F)
    hGjet hULp hGLp hgraph hgraphBound
  have hgraphFin :
      (∑ k : Fin (b + 1), ∑ i : Fin 5, ‖(hgraph k.val i).toLp
        (n06CubicGraphFields (fun p => cylinderWeight p.1)
          (mixedDerivative 0 k.val U) i)‖ ^ 2) ≤
        16384 * K ^ 10 *
          ((∑ k : Fin (b + 1), ‖(hGLp k.val).toLp (mixedDerivative 0 k.val G)‖ ^ 2) +
            ∑ k : Fin (b + 1), ‖(hULp k.val).toLp (mixedDerivative 0 k.val U)‖ ^ 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ∑ i : Fin 5,
        ‖(hgraph k i).toLp (n06CubicGraphFields (fun p => cylinderWeight p.1)
          (mixedDerivative 0 k U) i)‖ ^ 2),
      Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        ‖(hGLp k).toLp (mixedDerivative 0 k G)‖ ^ 2),
      Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        ‖(hULp k).toLp (mixedDerivative 0 k U)‖ ^ 2)]
    exact hgraphLp
  have hmem : ∀ᵐ p ∂cylinderWindowMeasure 0, p ∈ cylinderWindow 0 :=
    ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hstrip : ∀ᵐ p ∂cylinderWindowMeasure 0, p.1 ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hmem] with p hp
    exact ⟨hp.1.1.le, by simpa only [zero_add] using hp.1.2⟩
  obtain ⟨hPLp, hPbound⟩ := n06_unitCubic_divergence_angularJet_lp_bound
    hA hB hC hU b hδ hstrip hcoeff (fun k i => hgraph k.val i)
  refine ⟨hULp, hGLp, hPLp, ?_⟩
  have hcost : 0 ≤ 125 * n06AngularMultiplierCost b * δ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (n06AngularMultiplierCost_nonneg b)) (sq_nonneg δ)
  calc
    _ ≤ (125 * n06AngularMultiplierCost b * δ ^ 2) *
        ∑ k : Fin (b + 1), ∑ i : Fin 5, ‖(hgraph k.val i).toLp
          (n06CubicGraphFields (fun p => cylinderWeight p.1)
            (mixedDerivative 0 k.val U) i)‖ ^ 2 := hPbound
    _ ≤ (125 * n06AngularMultiplierCost b * δ ^ 2) *
        (16384 * K ^ 10 *
          ((∑ k : Fin (b + 1), ‖(hGLp k.val).toLp (mixedDerivative 0 k.val G)‖ ^ 2) +
            ∑ k : Fin (b + 1), ‖(hULp k.val).toLp (mixedDerivative 0 k.val U)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hgraphFin hcost
    _ = _ := by ring

end ContinuousFlexibility.Analysis
