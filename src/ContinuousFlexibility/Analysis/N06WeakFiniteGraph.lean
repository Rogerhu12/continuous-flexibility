import ContinuousFlexibility.Analysis.N06WeakFiniteParseval

/-!
# The finite Fourier cylinder graph estimate for weak radial solutions

Every selected radial mode starts from its genuine L2 weak equation. The
same H2 representatives furnished by the weak graph theorem determine five
weighted fields by actual finite synthesis. All angular orders use the
explicit Fourier weight, with no smooth radial-source assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The scalar five-term quantity already controlled by the weak graph theorem. -/
def n06WeakModeGraphSquare (j : ℝ) (v : ℝ → ℝ) : ℝ :=
  (∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv v y) ^ 2) +
    (1 + j ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * v y ^ 2) +
    (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv v) y) ^ 2) +
    (1 + j ^ 2) ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * v y ^ 2) +
    (1 + j ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv v y ^ 2)

/-- The same representative, with its actual closed-interval regularity and ODE. -/
structure N06WeakModeRepresentative (a c V u F v : ℝ → ℝ) (j : ℝ) : Prop where
  ae_eq : u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v
  contDiffOne : ContDiff ℝ 1 v
  firstAC : AbsolutelyContinuousOnInterval (deriv v) 0 1
  memLp : MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1))
  firstMemLp : MemLp (deriv v) 2 (volume.restrict (Ioo (0 : ℝ) 1))
  secondMemLp : MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo (0 : ℝ) 1))
  ode : ∀ᵐ y ∂volume.restrict (Ioo (0 : ℝ) 1),
    -deriv (fun t => a t * deriv v t) y + j ^ 2 * c y * v y + V y * v y = F y

/-- The angular orders belonging to the five genuine cubic graph fields. -/
def n06WeakFiniteGraphShift : Fin 5 → ℕ := ![0, 1, 2, 0, 1]

/-- Weighted radial coefficients of the five graph fields; second derivatives
are the actual L2 derivatives of the chosen H2 representatives. -/
def n06WeakFiniteGraphCoefficients (v : ℕ → ℝ → ℝ) : Fin 5 → ℕ → ℝ → ℝ :=
  ![fun i y => cylinderWeight y ^ 2 * deriv (deriv (v i)) y,
    fun i y => (cylinderWeight y ^ 2 * Real.sqrt (cylinderWeight y)) * deriv (v i) y,
    fun i y => cylinderWeight y ^ 3 * v i y,
    fun i y => cylinderWeight y * deriv (v i) y,
    fun i y => (cylinderWeight y * Real.sqrt (cylinderWeight y)) * v i y]

/-- Actual finite reconstructions of all angular jets of the five graph fields. -/
def n06WeakFiniteGraphFields (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (k : ℕ) (r : Fin 5) : PolarPoint → ℝ :=
  r11bFiniteSynthesis s (n06WeakFiniteGraphCoefficients v r)
    (fun i => iteratedDeriv (k + n06WeakFiniteGraphShift r) (referenceAngularBasis i))

theorem n06WeakFiniteGraphFields_eq_angularJet
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (k : ℕ) (r : Fin 5) :
    n06WeakFiniteGraphFields s v k r =
      mixedDerivative 0 (k + n06WeakFiniteGraphShift r)
        (r11bFiniteSynthesis s (n06WeakFiniteGraphCoefficients v r) referenceAngularBasis) :=
  (n06_mixedAngularDerivative_finiteSynthesis s _ referenceAngularBasis
    (fun i _ => contDiff_referenceAngularBasis i) _).symm

theorem n06_weak_graphCoefficients_memLp (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hv₀ : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∀ r i, i ∈ s → MemLp (n06WeakFiniteGraphCoefficients v r i) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  intro r i hi
  have hd := cylinderWeight_continuous
  fin_cases r <;> simp only [n06WeakFiniteGraphCoefficients,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact n06_interval_memLp_mul_continuous (hv₂ i hi) (hd.pow 2)
  · exact n06_interval_memLp_mul_continuous (hv₁ i hi) ((hd.pow 2).mul hd.sqrt)
  · exact n06_interval_memLp_mul_continuous (hv₀ i hi) (hd.pow 3)
  · exact n06_interval_memLp_mul_continuous (hv₁ i hi) hd
  · exact n06_interval_memLp_mul_continuous (hv₀ i hi) (hd.mul hd.sqrt)

theorem n06_weak_finiteGraphFields_memLp (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hv₀ : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) (k : ℕ) (r : Fin 5) :
    MemLp (n06WeakFiniteGraphFields s v k r) 2 (cylinderWindowMeasure 0) := by
  rw [n06WeakFiniteGraphFields_eq_angularJet]
  exact n06_weak_even_angularJet_memLp s _
    (n06_weak_graphCoefficients_memLp s v hv₀ hv₁ hv₂ r) _

/-- The five actual volume norms have their exact modal Parseval expression. -/
theorem n06_weak_finiteGraphFields_norm_sq (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hv₀ : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2
      (volume.restrict (Ioo (0 : ℝ) 1)))
    (k : ℕ)
    (hgraph : ∀ r, MemLp (n06WeakFiniteGraphFields s v k r) 2 (cylinderWindowMeasure 0)) :
    (∑ r, ‖(hgraph r).toLp (n06WeakFiniteGraphFields s v k r)‖ ^ 2) =
      Real.pi * ∑ i ∈ s, ∑ r : Fin 5,
        ((2 * i : ℕ) : ℝ) ^ (2 * (k + n06WeakFiniteGraphShift r)) *
          ∫ y in (0 : ℝ)..1, n06WeakFiniteGraphCoefficients v r i y ^ 2 := by
  have hrow (r : Fin 5) :
      ‖(hgraph r).toLp (n06WeakFiniteGraphFields s v k r)‖ ^ 2 =
        Real.pi * ∑ i ∈ s,
          ((2 * i : ℕ) : ℝ) ^ (2 * (k + n06WeakFiniteGraphShift r)) *
            ∫ y in (0 : ℝ)..1, n06WeakFiniteGraphCoefficients v r i y ^ 2 := by
    have hmem := n06_weak_even_angularJet_memLp s _
      (n06_weak_graphCoefficients_memLp s v hv₀ hv₁ hv₂ r)
      (k + n06WeakFiniteGraphShift r)
    have heqLp : (hgraph r).toLp (n06WeakFiniteGraphFields s v k r) =
        hmem.toLp (mixedDerivative 0 (k + n06WeakFiniteGraphShift r)
          (r11bFiniteSynthesis s (n06WeakFiniteGraphCoefficients v r) referenceAngularBasis)) :=
      MemLp.toLp_congr (hgraph r) hmem (Eventually.of_forall fun p =>
        congrFun (n06WeakFiniteGraphFields_eq_angularJet s v k r) p)
    rw [heqLp]
    exact n06_weak_even_angularJet_norm_sq s _
      (n06_weak_graphCoefficients_memLp s v hv₀ hv₁ hv₂ r) _ hmem
  simp_rw [hrow]
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- Each five-field modal cost is bounded by the full scalar graph quantity.
The factor is exactly the actual angular derivative weight. -/
theorem n06_weak_graph_row_sum_le (v : ℕ → ℝ → ℝ) (i k : ℕ) (j : ℝ) :
    (∑ r : Fin 5, j ^ (2 * (k + n06WeakFiniteGraphShift r)) *
      ∫ y in (0 : ℝ)..1, n06WeakFiniteGraphCoefficients v r i y ^ 2) ≤
      j ^ (2 * k) * n06WeakModeGraphSquare j (v i) := by
  let G : ℝ := ∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv (v i) y) ^ 2
  let L : ℝ := ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * v i y ^ 2
  let D : ℝ := ∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv (v i)) y) ^ 2
  let B : ℝ := ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * v i y ^ 2
  let J : ℝ := ∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv (v i) y ^ 2
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg zero_le_one
    (fun y hy => mul_nonneg (pow_nonneg (cylinderWeight_nonneg hy) 3) (sq_nonneg _))
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg zero_le_one
    (fun y hy => mul_nonneg (pow_nonneg (cylinderWeight_nonneg hy) 6) (sq_nonneg _))
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg zero_le_one
    (fun y hy => mul_nonneg (pow_nonneg (cylinderWeight_nonneg hy) 5) (sq_nonneg _))
  have hI₁ : (∫ y in (0 : ℝ)..1,
      ((cylinderWeight y ^ 2 * Real.sqrt (cylinderWeight y)) * deriv (v i) y) ^ 2) = J := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hd : 0 ≤ cylinderWeight y := cylinderWeight_nonneg (by
      simpa only [uIcc_of_le zero_le_one] using hy)
    simp only [mul_pow, Real.sq_sqrt hd]
    ring
  have hI₂ : (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 3 * v i y) ^ 2) = B := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hI₄ : (∫ y in (0 : ℝ)..1,
      ((cylinderWeight y * Real.sqrt (cylinderWeight y)) * v i y) ^ 2) = L := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hd : 0 ≤ cylinderWeight y := cylinderWeight_nonneg (by
      simpa only [uIcc_of_le zero_le_one] using hy)
    simp only [mul_pow, Real.sq_sqrt hd]
    ring
  have hp₁ : j ^ (2 * (k + 1)) = j ^ (2 * k) * j ^ 2 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
  have hp₂ : j ^ (2 * (k + 2)) = j ^ (2 * k) * j ^ 4 := by
    rw [show 2 * (k + 2) = 2 * k + 4 by omega, pow_add]
  have heq : (∑ r : Fin 5, j ^ (2 * (k + n06WeakFiniteGraphShift r)) *
      ∫ y in (0 : ℝ)..1, n06WeakFiniteGraphCoefficients v r i y ^ 2) =
      j ^ (2 * k) * (D + j ^ 2 * J + j ^ 4 * B + G + j ^ 2 * L) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, n06WeakFiniteGraphShift,
      n06WeakFiniteGraphCoefficients, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', add_zero]
    rw [hI₁, hI₂, hI₄, hp₁, hp₂]
    dsimp only [G, D]
    ring
  rw [heq]
  change j ^ (2 * k) * (D + j ^ 2 * J + j ^ 4 * B + G + j ^ 2 * L) ≤
    j ^ (2 * k) * (G + (1 + j ^ 2) * L + D + (1 + j ^ 2) ^ 2 * B + (1 + j ^ 2) * J)
  apply mul_le_mul_of_nonneg_left _ ((even_two_mul k).pow_nonneg j)
  nlinarith [mul_nonneg (sq_nonneg j) hB]

/-- Per-mode graph bounds transfer to the actual five cylinder L2 fields. -/
theorem n06_weak_finite_graph_lp_bound_of_modes
    (s : Finset ℕ) (u F v : ℕ → ℝ → ℝ) (C : ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hF : ∀ i ∈ s, MemLp (F i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₀ : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2
      (volume.restrict (Ioo (0 : ℝ) 1)))
    (hmode : ∀ i ∈ s, n06WeakModeGraphSquare (((2 * i : ℕ) : ℝ)) (v i) ≤
      C * ((∫ y in (0 : ℝ)..1, F i y ^ 2) + ∫ y in (0 : ℝ)..1, u i y ^ 2))
    (k : ℕ)
    (hU : MemLp (mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis)) 2
      (cylinderWindowMeasure 0))
    (hG : MemLp (mixedDerivative 0 k (r11bFiniteSynthesis s F referenceAngularBasis)) 2
      (cylinderWindowMeasure 0))
    (hgraph : ∀ r, MemLp (n06WeakFiniteGraphFields s v k r) 2 (cylinderWindowMeasure 0)) :
    (∑ r, ‖(hgraph r).toLp (n06WeakFiniteGraphFields s v k r)‖ ^ 2) ≤
      C * (‖hG.toLp (mixedDerivative 0 k (r11bFiniteSynthesis s F referenceAngularBasis))‖ ^ 2 +
        ‖hU.toLp (mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis))‖ ^ 2) := by
  let w : ℕ → ℝ := fun i => ((2 * i : ℕ) : ℝ) ^ (2 * k)
  have hw (i : ℕ) : 0 ≤ w i := (even_two_mul k).pow_nonneg _
  have hsum : (∑ i ∈ s, w i *
      (C * ((∫ y in (0 : ℝ)..1, F i y ^ 2) + ∫ y in (0 : ℝ)..1, u i y ^ 2))) =
      C * ((∑ i ∈ s, w i * ∫ y in (0 : ℝ)..1, F i y ^ 2) +
        ∑ i ∈ s, w i * ∫ y in (0 : ℝ)..1, u i y ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ = Real.pi * ∑ i ∈ s, ∑ r : Fin 5,
        ((2 * i : ℕ) : ℝ) ^ (2 * (k + n06WeakFiniteGraphShift r)) *
          ∫ y in (0 : ℝ)..1, n06WeakFiniteGraphCoefficients v r i y ^ 2 :=
      n06_weak_finiteGraphFields_norm_sq s v hv₀ hv₁ hv₂ k hgraph
    _ ≤ Real.pi * ∑ i ∈ s, w i * n06WeakModeGraphSquare (((2 * i : ℕ) : ℝ)) (v i) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      exact Finset.sum_le_sum (fun i _ => n06_weak_graph_row_sum_le v i k _)
    _ ≤ Real.pi * ∑ i ∈ s, w i *
        (C * ((∫ y in (0 : ℝ)..1, F i y ^ 2) + ∫ y in (0 : ℝ)..1, u i y ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hmode i hi) (hw i))
    _ = _ := by
      rw [hsum, n06_weak_even_angularJet_norm_sq s F hF k hG,
        n06_weak_even_angularJet_norm_sq s u hu k hU]
      dsimp only [w]
      ring

/-- Genuine L2 weak modal equations give the finite cylinder graph bound at all
angular orders. The representatives and every L2 membership are constructed. -/
theorem n06_weak_even_finite_graph_bound
    (s : Finset ℕ) (u F : ℕ → ℝ → ℝ)
    {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hu : ∀ i ∈ s, MemLp (u i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hF : ∀ i ∈ s, MemLp (F i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hweak : ∀ i ∈ s, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 →
        (∫ y in (0 : ℝ)..1, u i y * (-deriv (fun t => a t * deriv φ t) y +
          ((((2 * i : ℕ) : ℝ)) ^ 2 * c y + V y) * φ y)) =
            ∫ y in (0 : ℝ)..1, F i y * φ y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    ∃ v : ℕ → ℝ → ℝ,
      (∀ i ∈ s, N06WeakModeRepresentative a c V (u i) (F i) (v i) (((2 * i : ℕ) : ℝ))) ∧
      (∀ k : ℕ, mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis)
        =ᵐ[cylinderWindowMeasure 0]
          mixedDerivative 0 k (r11bFiniteSynthesis s v referenceAngularBasis)) ∧
      ∃ hULp : ∀ k : ℕ, MemLp
          (mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis)) 2
            (cylinderWindowMeasure 0),
      ∃ hFLp : ∀ k : ℕ, MemLp
          (mixedDerivative 0 k (r11bFiniteSynthesis s F referenceAngularBasis)) 2
            (cylinderWindowMeasure 0),
      ∃ hgraph : ∀ k : ℕ, ∀ r : Fin 5,
          MemLp (n06WeakFiniteGraphFields s v k r) 2 (cylinderWindowMeasure 0),
        ∀ b : ℕ,
          (∑ k : Fin (b + 1), ∑ r : Fin 5,
            ‖(hgraph k.val r).toLp (n06WeakFiniteGraphFields s v k.val r)‖ ^ 2) ≤
            16384 * K ^ 10 *
              ((∑ k : Fin (b + 1), ‖(hFLp k.val).toLp
                (mixedDerivative 0 k.val (r11bFiniteSynthesis s F referenceAngularBasis))‖ ^ 2) +
                ∑ k : Fin (b + 1), ‖(hULp k.val).toLp
                  (mixedDerivative 0 k.val (r11bFiniteSynthesis s u referenceAngularBasis))‖ ^ 2) := by
  classical
  have hex (i : ℕ) : ∃ v : ℝ → ℝ, i ∈ s →
      N06WeakModeRepresentative a c V (u i) (F i) v (((2 * i : ℕ) : ℝ)) ∧
      n06WeakModeGraphSquare (((2 * i : ℕ) : ℝ)) v ≤
        16384 * K ^ 10 *
          ((∫ y in (0 : ℝ)..1, F i y ^ 2) + ∫ y in (0 : ℝ)..1, u i y ^ 2) := by
    by_cases hi : i ∈ s
    · obtain ⟨v, huv, hv, hvAC, hv₀, hv₁, hv₂, hode, hbound⟩ :=
        n06_weakGraphStatement a c V q (u i) (F i) (((2 * i : ℕ) : ℝ)) K
          ha hc hV hq (hu i hi) (hF i hi) (hweak i hi)
          hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
      exact ⟨v, fun _ => ⟨⟨huv, hv, hvAC, hv₀, hv₁, hv₂, hode⟩, hbound⟩⟩
    · exact ⟨0, fun his => False.elim (hi his)⟩
  choose v hv using hex
  have hv₀ (i : ℕ) (hi : i ∈ s) := (hv i hi).1.memLp
  have hv₁ (i : ℕ) (hi : i ∈ s) := (hv i hi).1.firstMemLp
  have hv₂ (i : ℕ) (hi : i ∈ s) := (hv i hi).1.secondMemLp
  let hULp (k : ℕ) := n06_weak_even_angularJet_memLp s u hu k
  let hFLp (k : ℕ) := n06_weak_even_angularJet_memLp s F hF k
  let hgraph (k : ℕ) (r : Fin 5) := n06_weak_finiteGraphFields_memLp s v hv₀ hv₁ hv₂ k r
  refine ⟨v, fun i hi => (hv i hi).1, ?_, hULp, hFLp, hgraph, ?_⟩
  · intro k
    rw [n06_mixedAngularDerivative_finiteSynthesis s u referenceAngularBasis
        (fun i _ => contDiff_referenceAngularBasis i) k,
      n06_mixedAngularDerivative_finiteSynthesis s v referenceAngularBasis
        (fun i _ => contDiff_referenceAngularBasis i) k]
    exact n06_weak_finiteSynthesis_congr_ae s u v _ (fun i hi => (hv i hi).1.ae_eq)
  · intro b
    calc
      _ ≤ ∑ k : Fin (b + 1), (16384 * K ^ 10) *
          (‖(hFLp k.val).toLp
              (mixedDerivative 0 k.val (r11bFiniteSynthesis s F referenceAngularBasis))‖ ^ 2 +
            ‖(hULp k.val).toLp
              (mixedDerivative 0 k.val (r11bFiniteSynthesis s u referenceAngularBasis))‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        exact n06_weak_finite_graph_lp_bound_of_modes s u F v (16384 * K ^ 10)
          hu hF hv₀ hv₁ hv₂ (fun i hi => (hv i hi).2) k.val
          (hULp k.val) (hFLp k.val) (hgraph k.val)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]

end ContinuousFlexibility.Analysis
