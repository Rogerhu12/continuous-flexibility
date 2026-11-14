import ContinuousFlexibility.Analysis.N04PositiveGeometryTransportSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryJointNormalization
import ContinuousFlexibility.Analysis.N01cParameterCalculus

/-!
# Positive parameter mixed jets of the actual transports

A scalar projection of the same genuine joint transport has the same
sample envelope. Appending the actual radial and angular directions
keeps the parameter arity at its requested order, and spends only the
saved final spatial power.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The projection and spatial-slot budget are independent of the
atlas. Keeping them here avoids unfolding a stored transport while
splitting the pure-slot conditions or normalizing its scalar power. -/
private theorem projectedMixed_of_savedWords
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E × PolarPoint → PolarPoint}
    (J : SmoothDirections (U ×ˢ univ) f)
    (hU : IsOpen U) (hc : Convex ℝ (U ×ˢ (univ : Set PolarPoint)))
    (p : ℕ → Seminorm ℝ E) (low high K s shift : ℕ)
    (L : PolarPoint →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (k : ℕ) (hk : 0 < k) (hkK : k ≤ K)
    (a b : ℕ) (hab : a + b ≤ s) (x : E) (hx : x ∈ U) (q : PolarPoint)
    (hraw : ∀ R : ℝ, 1 ≤ R → p high x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ K + s + 1 →
      ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ u : Fin n → E × PolarPoint,
      (∀ j, if w.isState j then (u j).2 = 0 else (u j).1 = 0) →
      (∀ j, p low (u j).1 ≤ 1 ∧ p high (u j).1 ≤ R ∧ ‖(u j).2‖ ≤ 1) →
      ‖J.D n (x, q) u‖ ≤ M * parameterHeightWeight H w.stateArity *
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) ^
          (w.angleArity + shift * w.stateArity - 1))
    (Q : SmoothDirections U
      (fun z => mixedDerivative a b (fun y => L (f (z, y))) q)) :
    ∀ v : Fin k → E, (∀ j, p low (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p high x ≤ R → (∀ j, p high (v j) ≤ R) →
      |Q.D k x v| ≤ M * parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  let JP := smoothDirections_postcompCLM J L
  let exponent := ((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)
  have hscalar : ∀ R : ℝ, 1 ≤ R → p high (x - 0) ≤ R →
      ∀ n : ℕ, n ≤ k + a + b → ∀ w : StateAngleWord n, w.stateArity = k →
      ∀ u : Fin n → E × PolarPoint,
      (∀ j, p low (u j).1 ≤ 1) → (∀ j, p high (u j).1 ≤ R) →
      (∀ j, ‖(u j).2‖ ≤ 1) →
      (∀ j, w.isState j = false → (u j).1 = 0) →
      (∀ j, w.isState j = true → (u j).2 = 0) →
      |JP.D n (x, q) u| ≤ M * parameterHeightWeight H k * R ^ exponent := by
    intro R hR hxR n hn w hw u huL huH huS hu0 hu1
    have hnpos : 0 < n := by have := w.arity_sum; omega
    have hpure (j : Fin n) : if w.isState j then (u j).2 = 0 else (u j).1 = 0 := by
      cases hj : w.isState j
      · exact hu0 j hj
      · exact hu1 j hj
    have hr := hraw R hR (by simpa only [sub_zero] using hxR) n hnpos
      (by omega) w (hw.trans_le hkK) u hpure (fun j => ⟨huL j, huH j, huS j⟩)
    let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
    have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
    have hpower : t ^ (w.angleArity + shift * w.stateArity - 1) ≤ t ^ (a + b + shift * k) :=
      pow_le_pow_right₀ ht (by rw [hw]; have := w.arity_sum; omega)
    have hweight : parameterHeightWeight H w.stateArity = parameterHeightWeight H k :=
      congrArg (parameterHeightWeight H) hw
    have htpow : t ^ (a + b + shift * k) = R ^ exponent := by
      dsimp only [t, exponent]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
      congr 1
      ring
    have heq : M * parameterHeightWeight H w.stateArity * t ^ (a + b + shift * k) =
        M * parameterHeightWeight H k * R ^ exponent := by
      rw [hweight, htpow]
    have hproj : |JP.D n (x, q) u| ≤ ‖J.D n (x, q) u‖ := by
      change |L (J.D n (x, q) u)| ≤ _
      rw [← Real.norm_eq_abs]
      exact (L.le_opNorm _).trans
        (mul_le_of_le_one_left (norm_nonneg _) hL)
    exact (hproj.trans hr).trans ((mul_le_mul_of_nonneg_left hpower
      (mul_nonneg hM (parameterHeightWeight_nonneg hH _))).trans_eq heq)
  intro v hv R hR hxR hvR
  exact n04PositiveGeometry_mixedUnitPower_of_jointUnitPower JP hU isOpen_univ hc
    p low high 0 k a b x hx q (mem_univ _) hscalar Q v hv R hR
    (by simpa only [sub_zero] using hxR) hvR

theorem n04PositiveGeometry_transport_projected_mixed_sample_prefix
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (inverse : Bool) {base : ℕ} {ε : ℝ}
    (JF : ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint => if inverse then
          F.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C z.1) i z.2
          else F.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C z.1) i z.2))
    (hprefix : N04PositiveGeometryTransportSamplePrefix F inverse base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ L : PolarPoint →L[ℝ] ℝ, ‖L‖ ≤ 1 →
      ∀ k : ℕ, 0 < k → k ≤ K → ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ),
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun x => mixedDerivative a b (fun p => L (if inverse then
          F.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C x) i p
          else F.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C x) i p)) q),
      ∀ x ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low x ≤ 1 →
      ∀ v : Fin k → (StateDirections W.S × ℝ),
      (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) x ≤ R →
      (∀ j, pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) (v j) ≤ R) →
      |J.D k x v| ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  let low := hprefix.choose
  let p := pairGrading (sectorGrading W.S) realGrading
  have hU := sectorNeighborhood_isOpen W.S base ε ε
  have hc := (sectorNeighborhood_convex W.S base ε ε).prod (convex_univ : Convex ℝ (univ : Set PolarPoint))
  refine ⟨low, hprefix.choose_spec.1, fun K => ?_⟩
  let sd := hprefix.choose_spec.2 K
  let shift := sd.choose
  refine ⟨shift, fun s => ?_⟩
  let bd := sd.choose_spec s
  let A := bd.choose
  refine ⟨A, bd.choose_spec.1, ?_⟩
  intro i L hL k hk hkK a b hab q hq J x hx hxlow v hv R hR hxR hvR
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let E := W.U.E0 (W.U.sample (X.cell i))
  have hH : 0 ≤ H := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hM : 0 ≤ A * E ^ A := mul_nonneg (zero_le_one.trans bd.choose_spec.1)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  refine projectedMixed_of_savedWords (JF i) hU hc p low
    (low + s + shift * K + 1) K s shift L hL (A * E ^ A) H hM hH
    k hk hkK a b hab x hx q ?_ J v hv R hR hxR hvR
  intro R' hR' hxR' n hn hnN w hw u hpure hbox
  exact bd.choose_spec.2 i (JF i) x hx hxlow q hq R' hR' hxR'
    n hn hnN w hw u hpure hbox

end ContinuousFlexibility.Analysis
