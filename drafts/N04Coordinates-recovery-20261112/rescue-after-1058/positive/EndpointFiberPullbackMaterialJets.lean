import ContinuousFlexibility.Analysis.AngularFiberMaterialJetBounds
import ContinuousFlexibility.Analysis.EndpointFiberLinearJetEnvelope
import ContinuousFlexibility.Analysis.EndpointFiberPullbackAssembly

/-!
# Material jets of the same radial inverse-coordinate interpolation

The high angular derivatives of the actual inverse pullback supply the
finite radial Taylor data of the already selected collars. Their true
widths are retained. Only the estimate coefficient depends on the output
order; the low state order and derivative loss are common to all orders.
The high state grading remains a single factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

/-- The width and angular inverse costs are low numerical inputs. The
positive forward jets are source estimates, not a bound on the output
radial map. In particular the displayed interpolation is never reselected. -/
theorem endpointFiberPullback_displacementJets_le_material
    {Z : Type} [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ Z} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss n : ℕ) :
    ∃ base loss : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ L : ℝ, 0 ≤ L →
      ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ z : Z, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ l r c d κφ κX Mσ : ℝ,
        l < c → c < d → d < r → r - l ≤ L → 0 < κφ → 0 < κX → 0 ≤ Mσ →
        κφ⁻¹ ≤ K * W ^ K →
        (∀ side, (endpointFiberWidths n l r c d κX Mσ side)⁻¹ ≤ K * W ^ K) →
      ∀ (φ : PolarPoint → ℝ) (X : Bool → PolarPoint → ℝ),
        ContDiff ℝ ∞ φ → (∀ side, ContDiff ℝ ∞ (X side)) →
        (∀ q : PolarPoint, 0 < deriv (fun θ => φ (q.1, θ)) q.2) →
        (∀ x θ, φ (x, θ + Real.pi) = φ (x, θ) + Real.pi) →
        (∀ (side : Bool) (θ : ℝ),
          X side (if side then r else l, θ) = if side then r else l) →
        (∀ (side : Bool) (θ : ℝ),
          κφ ≤ angularPartial φ (if side then r else l, θ)) →
        (∀ (side : Bool) (k : ℕ), 1 ≤ k → ∀ θ : ℝ,
          ‖iteratedFDeriv ℝ k φ (if side then r else l, θ)‖ ≤
            A k * W ^ (A k) * (1 + p (k + inputLoss) z)) →
        (∀ (side : Bool) (k : ℕ), 1 ≤ k → ∀ θ : ℝ,
          ‖iteratedFDeriv ℝ k (X side) (if side then r else l, θ)‖ ≤
            A k * W ^ (A k) * (1 + p (k + inputLoss) z)) →
        ∀ N : ℕ, ∀ q : PolarPoint, q.1 ∈ Icc l r →
          ‖iteratedFDeriv ℝ N
            (fun x => endpointFiberPullbackCoordinate n φ X l r c d κX Mσ x - x.1) q‖ ≤
              B N * W ^ (B N) * (1 + p (N + loss) z) := by
  classical
  obtain ⟨base, pullLoss, hpullback⟩ :=
    angularFiberPullback_positiveJets_le_material hp hI inputLoss
  refine ⟨base, n + 1 + pullLoss, ?_⟩
  intro K hK L hL A hA
  obtain ⟨P, hP, hPbound⟩ := hpullback K hK A hA
  let R : ℕ → ℝ := fun N => 1 + ∑ k ∈ Finset.range (N + (n + 1) + 1), P k
  have hR (N : ℕ) : 1 ≤ R N :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => (hP k).le)
  have hPR (N k : ℕ) (hk : k ≤ N + (n + 1)) : P k ≤ R N :=
    (Finset.single_le_sum (fun j _ => (hP j).le)
      (Finset.mem_range.mpr (by omega : k < N + (n + 1) + 1))).trans
      (le_add_of_nonneg_left zero_le_one)
  choose C hC hcollar using fun N =>
    exists_endpointFiberInterpolation_linear_jet_envelope n N
  choose B hB hpack using fun N => coefficientEnvelope_pack
    (C N * (1 + L) * K ^ (2 * N + 1) * R N)
    (K * ((2 * N + 1 : ℕ) : ℝ) + R N)
  refine ⟨B, hB, ?_⟩
  intro z hz W hW l r c d κφ κX Mσ hlc hcd hdr hspan hκφ hκX hMσ hκinv hη
    φ X hφ hX hpositive hperiod hvalue hangle hφraw hXraw
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  let e : Bool → ℝ := fun side => if side then r else l
  let F : Bool → PolarPoint → ℝ := fun side => angularFiberPullback φ (X side)
  let D : Bool → ℕ → ℝ → ℝ := fun side => radialBoundaryJet (F side) (e side)
  have hF (side : Bool) : ContDiff ℝ ∞ (F side) :=
    contDiff_angularFiberPullback Real.pi_ne_zero hφ (hX side) hpositive hperiod
  have hD (side : Bool) (j : ℕ) : ContDiff ℝ ∞ (D side j) :=
    contDiff_radialBoundaryJet (hF side) (e side) j
  have hDvalue (side : Bool) (θ : ℝ) : D side 0 θ = e side := by
    change iteratedDeriv 0 (fun x => F side (x, θ)) (e side) = e side
    simpa only [iteratedDeriv_zero] using
      angularFiberPullback_boundary (φ := φ) (hvalue side) θ
  have hFbound (side : Bool) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (F side) (e side, θ)‖ ≤
        P k * W ^ (P k) * (1 + p (k + pullLoss) z) :=
    hPbound z hz W hW φ (X side) Real.pi Real.pi_ne_zero hφ (hX side)
      hpositive hperiod (e side, θ) κφ hκφ hκinv
      (hangle side (parameterizedCircleInverse φ (e side, θ)))
      (fun k hk => hφraw side k hk (parameterizedCircleInverse φ (e side, θ)))
      (fun k hk => hXraw side k hk (parameterizedCircleInverse φ (e side, θ))) k hk
  have hU : 1 ≤ K * W ^ K := by
    simpa only [one_mul] using
      mul_le_mul hK (Real.one_le_rpow hW hK0) zero_le_one hK0
  intro N q hq
  let V : ℝ := R N * W ^ (R N) * (1 + p (N + (n + 1 + pullLoss)) z)
  have hR0 : 0 ≤ R N := zero_le_one.trans (hR N)
  have hG : 1 ≤ 1 + p (N + (n + 1 + pullLoss)) z :=
    le_add_of_nonneg_right (apply_nonneg _ _)
  have hRG : 1 ≤ R N * W ^ (R N) := by
    simpa only [one_mul] using
      mul_le_mul (hR N) (Real.one_le_rpow hW hR0) zero_le_one hR0
  have hV : 1 ≤ V := by
    simpa only [one_mul] using
      mul_le_mul hRG hG zero_le_one (zero_le_one.trans hRG)
  have hraise (k : ℕ) (hk : k ≤ N + (n + 1)) :
      P k * W ^ (P k) * (1 + p (k + pullLoss) z) ≤ V := by
    apply mul_le_mul
      (mul_le_mul (hPR N k hk)
        (Real.rpow_le_rpow_of_exponent_le hW (hPR N k hk))
        (Real.rpow_nonneg hW0.le _) hR0)
      (add_le_add_left (hp (by omega : k + pullLoss ≤ N + (n + 1 + pullLoss)) z) 1)
      (add_nonneg zero_le_one (apply_nonneg _ _))
      (mul_nonneg hR0 (Real.rpow_nonneg hW0.le _))
  have htrace (side : Bool) (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n + 1)
      (b : ℕ) (hb : b ≤ N) (θ : ℝ) : |iteratedDeriv b (D side j) θ| ≤ V := by
    calc
      _ = |mixedDerivative j b (F side) (e side, θ)| := by
        dsimp only [D]
        rw [iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
          isOpen_univ (hF side).contDiffOn (e side) (fun _ => mem_univ _) j b θ]
      _ ≤ ‖iteratedFDeriv ℝ (j + b) (F side) (e side, θ)‖ :=
        abs_mixedDerivative_le_norm_iteratedFDeriv isOpen_univ
          (hF side).contDiffOn j b (mem_univ _)
      _ ≤ P (j + b) * W ^ (P (j + b)) * (1 + p (j + b + pullLoss) z) :=
        hFbound side (j + b) (by omega) θ
      _ ≤ V := hraise (j + b) (by omega)
  have hbound := hcollar N hU hV hlc hcd hdr hκX hMσ hη D
    (fun side j _ => hD side j) hDvalue htrace N le_rfl q hq
  calc
    _ ≤ C N * (1 + (r - l)) * (K * W ^ K) ^ (2 * N + 1) * V := hbound
    _ ≤ C N * (1 + L) * (K * W ^ K) ^ (2 * N + 1) * V :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add_left hspan 1) (zero_le_one.trans (hC N)))
          (pow_nonneg (zero_le_one.trans hU) _)) (zero_le_one.trans hV)
    _ = (C N * (1 + L) * K ^ (2 * N + 1) * R N) *
        W ^ (K * ((2 * N + 1 : ℕ) : ℝ) + R N) *
          (1 + p (N + (n + 1 + pullLoss)) z) := by
      dsimp only [V]
      rw [mul_pow, ← Real.rpow_mul_natCast hW0.le K (2 * N + 1), Real.rpow_add hW0]
      ring
    _ ≤ B N * W ^ (B N) * (1 + p (N + (n + 1 + pullLoss)) z) :=
      mul_le_mul_of_nonneg_right (hpack N W hW) (zero_le_one.trans hG)

end ContinuousFlexibility.Analysis
