import ContinuousFlexibility.Radial.CentralBufferGeometry
import ContinuousFlexibility.Radial.CentralBufferInverses
import ContinuousFlexibility.Radial.CentralModelPhysicalColumn

/-!
# Choosing one actual central truncation for every even mode

The finite full-inverse bound is chosen first. A single model radius
then contains the genuine compact column and satisfies R09 smallness
uniformly for every positive even frequency. The radius can exceed any
specified lower bound. Its containment in a separately connected radial
central patch is a different geometric assertion.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

/-- A uniform algebraic upper bound sufficient to choose the action
without an implicit dependence on the frequency. -/
theorem centralBuffer_smallness_bound {j T B₀ : ℝ}
    (hj : 0 ≤ j) (hT : 0 < T) (hB₀ : 0 ≤ B₀) :
    B₀ * centralBufferMass j T ^ 2 * exp (-centralBufferAction j T) ≤
      16 * B₀ * exp 6 / T ^ 2 := by
  have ht : 0 ≤ j * T ^ 2 / 16 := by positivity
  have hlin : j * T ^ 2 / 16 ≤ exp (j * T ^ 2 / 16) := by
    linarith [add_one_le_exp (j * T ^ 2 / 16)]
  have hs : (j * T ^ 2 / 16) ^ 2 ≤ exp (j * T ^ 2 / 8) := by
    calc
      _ ≤ exp (j * T ^ 2 / 16) ^ 2 := pow_le_pow_left₀ ht hlin 2
      _ = _ := by rw [pow_two, ← exp_add]; congr 1 <;> ring
  have he : exp (-centralBufferAction j T) = exp 6 / exp (j * T ^ 2 / 8) := by
    unfold centralBufferAction
    rw [show -(j * T ^ 2 / 8 - 6) = 6 - j * T ^ 2 / 8 by ring, exp_sub]
  rw [he]
  calc
    B₀ * centralBufferMass j T ^ 2 * (exp 6 / exp (j * T ^ 2 / 8)) =
        (B₀ * exp 6 * centralBufferMass j T ^ 2) / exp (j * T ^ 2 / 8) := by ring
    _ ≤ 16 * B₀ * exp 6 / T ^ 2 := by
      apply (div_le_div_iff₀ (exp_pos _) (sq_pos_of_pos hT)).mpr
      calc
        B₀ * exp 6 * centralBufferMass j T ^ 2 * T ^ 2 =
            (16 * B₀ * exp 6) * (j * T ^ 2 / 16) ^ 2 := by
          unfold centralBufferMass
          ring
        _ ≤ (16 * B₀ * exp 6) * exp (j * T ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hs (by positivity)

/-- A single radius contains any compact column and meets the smallness
condition for all j ≥ 2, after the finite inverse constant is fixed. -/
theorem exists_centralBuffer_radius {f : ℝ → ℝ} (hc : HasCompactSupport f)
    {B₀ ε : ℝ} (hB₀ : 0 ≤ B₀) (hε : 0 < ε) (Tmin : ℝ) :
    ∃ T : ℝ, 8 ≤ T ∧ Tmin ≤ T ∧
      Function.support f ⊆ Ioo (-T / 2) (T / 2) ∧
      ∀ j : ℝ, 2 ≤ j →
        B₀ * centralBufferMass j T ^ 2 * exp (-centralBufferAction j T) < ε := by
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : ℝ => x) (tsupport f))
  let Q : ℝ := 16 * B₀ * exp 6 / ε
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let T : ℝ := 9 + 2 * |R| + |Tmin| + Q
  have hT : 8 ≤ T := by dsimp [T]; linarith [abs_nonneg R, abs_nonneg Tmin]
  have hTpos : 0 < T := by linarith
  have hTmin : Tmin ≤ T := by
    dsimp [T]
    linarith [le_abs_self Tmin, abs_nonneg R]
  have hRT : |R| < T / 2 := by dsimp [T]; linarith [abs_nonneg Tmin]
  have hQT : Q + 1 ≤ T := by dsimp [T]; linarith [abs_nonneg R, abs_nonneg Tmin]
  have hQsq : Q < T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
  have hsmall : 16 * B₀ * exp 6 / T ^ 2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hTpos)).mpr
    have hd : 16 * B₀ * exp 6 / ε < T ^ 2 := hQsq
    have hm := (div_lt_iff₀ hε).mp hd
    nlinarith
  refine ⟨T, hT, hTmin, ?_, ?_⟩
  · intro x hx
    have hnorm : |x| ≤ R := by
      simpa only [id_eq, Real.norm_eq_abs] using hR x (subset_tsupport f hx)
    have hxabs : |x| < T / 2 := (hnorm.trans (le_abs_self R)).trans_lt hRT
    change -T / 2 < x ∧ x < T / 2
    simpa only [neg_div] using abs_lt.mp hxabs
  · intro j hj
    exact (centralBuffer_smallness_bound (by linarith) hTpos hB₀).trans_lt hsmall

/-- Actual buffer data for the true physical column, with a common radius
and a common finite full-inverse bound for all even modes. -/
theorem exists_actualCentralModelBuffers {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (hpair : (∫ r : ℝ, g r * centralKernelHeight r) ≠ 0)
    (Tmin : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B₀ T : ℝ, 0 < B₀ ∧ 8 ≤ T ∧ Tmin ≤ T ∧
      ∀ n : ℕ, 1 ≤ n →
        let B := centralModelBuffer (2 * (n : ℝ)) T B₀ (centralModelBordered n)
          (centralModelPhysicalColumn hscale hg hc hp) (centralModelPhysicalColumnFunction scale g)
        BufferHypotheses B ∧
          ∀ i, B.B₀ * B.mass i ^ 2 * exp (-B.action i) < ε := by
  obtain ⟨B₀, hB₀, hfull⟩ := exists_central_even_full_inverse_bound
    (centralModelPhysicalColumn hscale hg hc hp)
    (centralModelPhysicalColumn_ground_pairing_ne_zero hscale hg hc hp hpair)
  obtain ⟨T, hT, hTmin, hsupp, hsmall⟩ := exists_centralBuffer_radius
    (centralModelPhysicalColumnFunction_hasCompactSupport scale hc hp) hB₀.le hε Tmin
  refine ⟨B₀, T, hB₀, hT, hTmin, ?_⟩
  intro n hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hj : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  obtain ⟨H, hHnorm, hHsolve, hHunique⟩ := hfull n hn
  refine ⟨centralModelBuffer_hypotheses (centralModelBordered n)
    (centralModelPhysicalColumn hscale hg hc hp) (centralModelPhysicalColumnFunction scale g)
    hj hT hB₀ (contDiff_centralModelPhysicalColumnFunction hscale hg)
    (centralModelPhysicalColumnFunction_hasCompactSupport scale hc hp)
    (centralModelPhysicalColumn_ae hscale hg hc hp) hsupp H hHnorm hHsolve hHunique, ?_⟩
  intro i
  simpa only [centralModelBuffer] using hsmall (2 * (n : ℝ)) hj

/-- R09 applies with its single fixed layer constant 64. The finite
inverse bound and then the common truncation radius are chosen in that
order; no smallness condition is an additional input. -/
theorem exists_actualCentralModelBuffer_compression (hR09 : R09Statement)
    {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (hpair : (∫ r : ℝ, g r * centralKernelHeight r) ≠ 0) (Tmin : ℝ) :
    ∃ C ε B₀ T : ℝ, 0 < C ∧ 0 < ε ∧ 0 < B₀ ∧ 8 ≤ T ∧ Tmin ≤ T ∧
      ∀ n : ℕ, 1 ≤ n →
        let B := centralModelBuffer (2 * (n : ℝ)) T B₀ (centralModelBordered n)
          (centralModelPhysicalColumn hscale hg hc hp) (centralModelPhysicalColumnFunction scale g)
        BufferHypotheses B ∧
          (∀ i, B.B₀ * B.mass i ^ 2 * exp (-B.action i) < ε) ∧
          BufferCompressionConclusion B C := by
  obtain ⟨C, ε, hC, hε, hcompress⟩ := hR09 64 (by norm_num)
  obtain ⟨B₀, T, hB₀, hT, hTmin, hbuffers⟩ :=
    exists_actualCentralModelBuffers hscale hg hc hp hpair Tmin hε
  refine ⟨C, ε, B₀, T, hC, hε, hB₀, hT, hTmin, ?_⟩
  intro n hn
  obtain ⟨hB, hsmall⟩ := hbuffers n hn
  refine ⟨hB, hsmall, hcompress _ ?_ hB hsmall⟩
  change (64 : ℝ) ≤ 64
  exact le_rfl

/-- The column and its scale are those of the existing joint geometry.
The resulting cuts are model-coordinate cuts; this theorem does not
assert their containment in the finite connected central patch. -/
theorem ConnectedReferenceGeometry.exists_centralBuffer_compression
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hR09 : R09Statement) (Tmin : ℝ) :
    ∃ scale amplitude : ℝ, ∃ hscale : 0 < scale,
      amplitude ≠ 0 ∧
      EqOn Γ.reference.w (centralRadialProfile scale) (Ioo Γ.centralLeft Γ.centralRight) ∧
      EqOn Γ.reference.phi (fun r => amplitude * centralKernelHeight r)
        (Ioo Γ.centralLeft Γ.centralRight) ∧
      ∃ (hg : ContDiff ℝ ∞ (referenceColumn Γ.reference))
        (hc : HasCompactSupport (referenceColumn Γ.reference))
        (hp : tsupport (referenceColumn Γ.reference) ⊆ Ioi 0),
        ∃ C ε B₀ T : ℝ, 0 < C ∧ 0 < ε ∧ 0 < B₀ ∧ 8 ≤ T ∧ Tmin ≤ T ∧
          ∀ n : ℕ, 1 ≤ n →
            let B := centralModelBuffer (2 * (n : ℝ)) T B₀ (centralModelBordered n)
              (centralModelPhysicalColumn hscale hg hc hp)
              (centralModelPhysicalColumnFunction scale (referenceColumn Γ.reference))
            BufferHypotheses B ∧
              (∀ i, B.B₀ * B.mass i ^ 2 * exp (-B.action i) < ε) ∧
              BufferCompressionConclusion B C := by
  obtain ⟨scale, amplitude, hscale, hamplitude, hwmodel, hφmodel,
      hg, hc, hp, hpair, _⟩ := ConnectedReferenceGeometry.centralInverseRealization hΓ
  refine ⟨scale, amplitude, hscale, hamplitude, hwmodel, hφmodel, hg, hc, hp, ?_⟩
  apply exists_actualCentralModelBuffer_compression hR09 hscale hg hc hp _ Tmin
  rw [hpair]
  exact div_ne_zero one_ne_zero hamplitude

end ContinuousFlexibility.Radial
