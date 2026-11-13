import ContinuousFlexibility.Analysis.N04NegativeChartVariationSelection

/-!
# Every finite state prefix of the actual flow on one fixed domain

The induction changes only the additive state-order spatial loss and
the ordinary material polynomial. The input domain, the family of actual
flows, and the external height factor remain fixed. Losses of strict
lower state orders are selected before any spatial budget; finite
spatial constants are selected afterwards. This is the quantitative
closure of the genuine variational equations, with no lower-flow bounds
left among the hypotheses of the final theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q]

/-- A property of the genuine derivatives. Order zero has no assertion,
so a finite prefix includes it without introducing a new flow estimate. -/
def NegativeChartPositiveVariationOrderBounds
    (Θ : I → E × PolarPoint → ℝ) (γ : I → Q → E) (α : I → Q → ℝ)
    (x : I → Q) (H A : I → ℝ) (ρ : ℕ → I → ℝ)
    (admissible : ∀ n : ℕ, I → (Fin n → E) → Prop) (n D : ℕ) : Prop :=
  ∀ K : ℕ, ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧
    (0 < n → ∀ i : I, ∀ v : Fin n → E, admissible n i v →
      ∀ k, k ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ k (fun y : Q =>
          flowParameterField (Θ i) n (γ i y) v (t, α i y)) (x i)‖ ≤
            C * H i * A i ^ e * ρ K i ^ (D + k))

private theorem material_coefficient_mono {A C C' : ℝ} {e e' : ℕ}
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hCC' : C ≤ C') (hee' : e ≤ e') :
    C * A ^ e ≤ C' * A ^ e' :=
  mul_le_mul hCC' (pow_le_pow_right₀ hA hee')
    (pow_nonneg (zero_le_one.trans hA) _) (hC.trans hCC')

/-- Genuine strong induction on a fixed finite state prefix. The head bounds
refer only to derivatives of the original speed along the state-free
spatial flow. All positive state derivatives of that flow are proved
here by their actual ODE and its strict-lower finite forcing expansion. -/
theorem n04NegativeChart_actualVariation_all_orders (N : ℕ)
    (G Θ : I → E × PolarPoint → ℝ)
    (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (J : ∀ i, ContinuousTimeSpeedTower (univ : Set E) (G i))
    (hΘ : ∀ i, ContDiff ℝ ∞ (Θ i))
    (hinit : ∀ i q α, Θ i (q, (0, α)) = α)
    (hflow : ∀ i q t α, HasDerivAt (fun r => Θ i (q, (r, α)))
      (G i (q, (t, Θ i (q, (t, α))))) t)
    (γ : I → Q → E) (α : I → Q → ℝ)
    (hγ : ∀ i, ContDiff ℝ ∞ (γ i)) (hα : ∀ i, ContDiff ℝ ∞ (α i))
    (x : I → Q) (H A : I → ℝ) (ρ : ℕ → I → ℝ)
    (admissible : ∀ n : ℕ, I → (Fin n → E) → Prop)
    (hrestrict : ∀ n i v, admissible n i v → ∀ k (e : Fin k → Fin n),
      admissible k i (v ∘ e))
    {R Λ : ℝ} (hR : 1 ≤ R) (hΛ : 0 ≤ Λ)
    (hH : ∀ i, 0 ≤ H i) (hHR : ∀ i, H i ≤ R)
    (hA : ∀ i, 1 ≤ A i) (hρ : ∀ K i, 1 ≤ ρ K i)
    (hprimitive : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      |∫ r in (0 : ℝ)..t,
        flowVariationCoefficient (G i) (Θ i) (γ i (x i)) (r, α i (x i))| ≤ Λ)
    (hcoefficient : ∀ K : ℕ, ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧
      ∀ i j, 1 ≤ j → j ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : Q =>
          flowVariationCoefficient (G i) (Θ i) (γ i y) (t, α i y)) (x i)‖ ≤
            C * A i ^ e * ρ K i ^ j)
    (hhead : ∀ n : ℕ, n ≤ N → 0 < n → ∃ D : ℕ, ∀ K : ℕ,
      ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧ ∀ i (v : Fin n → E), admissible n i v →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ d : FlowForcingChoice n, ∀ j, j ≤ K →
          ‖iteratedFDeriv ℝ j (fun y : Q =>
            canonicalFlowForcingFactors (J i) (hΘ i) (γ i y) v t d 0 (α i y)) (x i)‖ ≤
              parameterHeightWeight (H i) d.2.card *
                (C * A i ^ e) * ρ K i ^ (D + j)) :
    ∀ n : ℕ, n ≤ N → ∃ D : ℕ,
      NegativeChartPositiveVariationOrderBounds Θ γ α x H A ρ admissible n D := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnN
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, fun K => ⟨1, 0, le_rfl, by omega⟩⟩
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    obtain ⟨D₀, hheads⟩ := hhead n hnN hn
    choose d hd using (fun m : Fin n => ih m m.isLt (m.isLt.le.trans hnN))
    let D : ℕ := D₀ + ∑ m : Fin n, d m
    have hD₀ : D₀ ≤ D := Nat.le_add_right _ _
    have hdD (m : Fin n) : d m ≤ D :=
      (Finset.single_le_sum (fun (l : Fin n) _ => Nat.zero_le (d l))
        (Finset.mem_univ m)).trans
        (Nat.le_add_left _ _)
    refine ⟨D * (n + 1), fun K => ?_⟩
    obtain ⟨Cκ, eκ, hCκ, hκ⟩ := hcoefficient K
    obtain ⟨C₀, e₀, hC₀, hh⟩ := hheads K
    choose C e hC hb using (fun m : Fin n => hd m K)
    obtain ⟨Cstep, hCstep, hstep⟩ :=
      n04NegativeChart_actualVariation_weighted_step (E := E) (Q := Q) n K hn
    let Cbase : ℝ := 1 + Cκ + C₀ + ∑ m : Fin n, C m
    let ebase : ℕ := eκ + e₀ + ∑ m : Fin n, e m
    have hsum : 0 ≤ ∑ m : Fin n, C m :=
      Finset.sum_nonneg (fun m _ => zero_le_one.trans (hC m))
    have hCbase : 1 ≤ Cbase := by dsimp only [Cbase]; linarith
    have hCκbase : Cκ ≤ Cbase := by dsimp only [Cbase]; linarith
    have hC₀base : C₀ ≤ Cbase := by dsimp only [Cbase]; linarith
    have hCbase' (m : Fin n) : C m ≤ Cbase := by
      have hs := Finset.single_le_sum
        (fun l (_ : l ∈ (Finset.univ : Finset (Fin n))) => zero_le_one.trans (hC l))
        (Finset.mem_univ m)
      dsimp only [Cbase]
      linarith
    have heκ : eκ ≤ ebase := by dsimp only [ebase]; omega
    have he₀ : e₀ ≤ ebase := by dsimp only [ebase]; omega
    have he (m : Fin n) : e m ≤ ebase := by
      have hs := Finset.single_le_sum (fun (l : Fin n) _ => Nat.zero_le (e l))
        (Finset.mem_univ m)
      change e m ≤ eκ + e₀ + ∑ l : Fin n, e l
      omega
    let p : ℕ := (n + 1) * (2 * K + 1)
    let Cfinal : ℝ := Cstep * Real.exp (2 * Λ) * (Cbase * R) ^ p
    have hCfinal : 1 ≤ Cfinal :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hCstep
          (Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) hΛ)))
        (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hCbase hR))
    refine ⟨Cfinal, ebase * p, hCfinal, fun _ i v hv k hk t ht => ?_⟩
    let M : ℝ := Cbase * A i ^ ebase
    have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hCbase (one_le_pow₀ (hA i))
    have hMR : 1 ≤ M * R := one_le_mul_of_one_le_of_one_le hM hR
    have hMle : M ≤ M * R := le_mul_of_one_le_right (zero_le_one.trans hM) hR
    have hκM (j : ℕ) (hj : 1 ≤ j) (hjK : j ≤ K)
        (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
        ‖iteratedFDeriv ℝ j (fun y : Q =>
          flowVariationCoefficient (G i) (Θ i) (γ i y) (r, α i y)) (x i)‖ ≤
            (M * R) * ρ K i ^ j :=
      (hκ i j hj hjK r hr).trans (mul_le_mul_of_nonneg_right
        ((material_coefficient_mono (hA i) (zero_le_one.trans hCκ) hCκbase heκ).trans hMle)
        (pow_nonneg (zero_le_one.trans (hρ K i)) _))
    have hheadsM (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
        (choice : FlowForcingChoice n) (j : ℕ) (hj : j ≤ K) :
        ‖iteratedFDeriv ℝ j (fun y : Q =>
          canonicalFlowForcingFactors (J i) (hΘ i) (γ i y) v r choice 0 (α i y)) (x i)‖ ≤
            parameterHeightWeight (H i) choice.2.card * M * ρ K i ^ (D + j) := by
      have hweight : 0 ≤ parameterHeightWeight (H i) choice.2.card :=
        parameterHeightWeight_nonneg (hH i) _
      exact (hh i v hv r hr choice j hj).trans
        (mul_le_mul
          (mul_le_mul_of_nonneg_left
            (material_coefficient_mono (hA i) (zero_le_one.trans hC₀) hC₀base he₀) hweight)
          (pow_le_pow_right₀ (hρ K i) (Nat.add_le_add_right hD₀ j))
          (pow_nonneg (zero_le_one.trans (hρ K i)) _)
          (mul_nonneg hweight (zero_le_one.trans hM)))
    have hlowerM (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
        (a : ℕ) (ha : 0 < a) (han : a < n) (emb : Fin a → Fin n)
        (j : ℕ) (hj : j ≤ K) :
        ‖iteratedFDeriv ℝ j (fun y : Q =>
          flowParameterField (Θ i) a (γ i y) (v ∘ emb) (r, α i y)) (x i)‖ ≤
            H i * M * ρ K i ^ (D + j) := by
      let m : Fin n := ⟨a, han⟩
      have hraw := hb m ha i (v ∘ emb) (hrestrict n i v hv a emb) j hj r hr
      have hmaterial : C m * A i ^ e m ≤ M :=
        material_coefficient_mono (hA i) (zero_le_one.trans (hC m)) (hCbase' m) (he m)
      calc
        _ ≤ C m * H i * A i ^ e m * ρ K i ^ (d m + j) := hraw
        _ = H i * (C m * A i ^ e m) * ρ K i ^ (d m + j) := by ring
        _ ≤ H i * M * ρ K i ^ (D + j) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmaterial (hH i))
            (pow_le_pow_right₀ (hρ K i) (Nat.add_le_add_right (hdD m) j))
            (pow_nonneg (zero_le_one.trans (hρ K i)) _)
            (mul_nonneg (hH i) (zero_le_one.trans hM))
    have hmarked (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :=
      n04NegativeChart_actualForcing_marked_factors (J i) (hΘ i) hn K D
        (γ i) (α i) v r (x i) (hH i) (hHR i) hM hR (hρ K i)
        (hheadsM r hr) (hlowerM r hr)
    have hactual := hstep (hG i) (J i) (hΘ i) (hinit i) (hflow i)
      (γ i) (α i) (hγ i) (hα i) v (x i) D (hH i) hMR (hρ K i)
      (hprimitive i) hκM hmarked k hk t ht
    refine hactual.trans_eq ?_
    dsimp only [Cfinal, M, p]
    simp only [mul_pow, ← pow_mul]
    ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_actualVariation_all_orders'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_actualVariation_all_orders
