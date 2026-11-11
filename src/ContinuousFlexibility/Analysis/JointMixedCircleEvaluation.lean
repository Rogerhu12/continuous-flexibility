import ContinuousFlexibility.Analysis.JointMixedDiagonalCalculus
import ContinuousFlexibility.Analysis.CircleJointEvaluation
import ContinuousFlexibility.Analysis.SmoothDirectionsConstantShift

/-!
# Identifying the angular boundary of an actual joint tower

Fixing a radius gives a genuine parameter tower. Its uniqueness
identifies it with the continuous point evaluation of any genuine
circle-valued tower representing the same function. Differentiating
this equality in the angle identifies all angular parameter jets.
The circle tower may depend on an arbitrary selector of radii.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {l h r : ℝ} {f : E × PolarPoint → ℝ} {g : E → H.Space}

/-- Equality of the underlying scalar values identifies every pure
parameter jet, for arbitrary tuples of parameter directions. -/
theorem SmoothDirections.jointJet_eq_circleDecoded
    (J : SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ)) f)
    (hH : IsCircleModel T γ H) (K : SmoothDirections U g)
    (m : ℕ) (hr : r ∈ Ioo l h)
    (heq : ∀ x ∈ U, ∀ θ, f (x, (r, θ)) = H.decode (g x) m θ)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (θ : ℝ) :
    J.D n (x, (r, θ)) (fun i => (v i, (0 : PolarPoint))) =
      H.decode (K.D n x v) m θ := by
  let P : SmoothDirections U (fun x => f (x, (r, θ))) :=
    (circleDecodedAngularDirections hH K 0 m θ).congrOn
      (fun x hx => by simpa only [iteratedDeriv_zero] using (heq x hx θ).symm)
  have hp : (r, θ) ∈ Ioo l h ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ θ⟩
  calc
    _ = P.D n x v := (J.pointTower_eq_jointJet K.open_domain (r, θ) hp P n x hx v).symm
    _ = _ := by
      change (circleDecodedAngularDirections hH K 0 m θ).D n x v = _
      simpa only [iteratedDeriv_zero] using circleDecodedAngularDirections_jet hH K 0 m θ n x v

/-- The zeroth radial order of the actual diagonal mixed jets is the
ordinary angular jet of the same circle-valued parameter derivative. -/
theorem jointMixedDiagonal_eq_circleAngularJet
    (J : SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ)) f)
    (hH : IsCircleModel T γ H) (K : SmoothDirections U g)
    (m : ℕ) (hr : r ∈ Ioo l h)
    (heq : ∀ x ∈ U, ∀ θ, f (x, (r, θ)) = H.decode (g x) m θ)
    (n b : ℕ) (x w : E) (hx : x ∈ U) (θ : ℝ) :
    jointMixedDiagonal J n 0 b x w (r, θ) =
      iteratedDeriv b (H.decode (K.D n x (fun _ => w)) m) θ := by
  have hfun : (fun θ => J.D n (x, (r, θ))
      (fun _ : Fin n => (w, (0 : PolarPoint)))) =
      H.decode (K.D n x (fun _ => w)) m := by
    funext φ
    exact J.jointJet_eq_circleDecoded hH K m hr heq n x hx (fun _ => w) φ
  simp only [jointMixedDiagonal, mixedDerivative, iteratedDeriv_zero]
  rw [hfun]

/-- A fixed scalar offset contributes only to the zeroth parameter jet. -/
theorem SmoothDirections.jointJet_eq_circleDecoded_add_const
    (J : SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ)) f)
    (hH : IsCircleModel T γ H) (K : SmoothDirections U g)
    (m : ℕ) (hr : r ∈ Ioo l h) (c : ℝ)
    (heq : ∀ x ∈ U, ∀ θ, f (x, (r, θ)) = c + H.decode (g x) m θ)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (θ : ℝ) :
    J.D n (x, (r, θ)) (fun i => (v i, (0 : PolarPoint))) =
      (if n = 0 then c else 0) + H.decode (K.D n x v) m θ := by
  have hp : (r, θ) ∈ Ioo l h ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ θ⟩
  cases n with
  | zero =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      have hv' : (fun i : Fin 0 => (v i, (0 : PolarPoint))) = Fin.elim0 :=
        Subsingleton.elim _ _
      rw [hv', J.zero (x, (r, θ)) ⟨hx, hp⟩, hv, K.zero x hx, if_pos rfl]
      exact heq x hx θ
  | succ n =>
      let P := J.freezeSpatial K.open_domain (r, θ) hp
      let Q := circleDecodedAngularDirections hH K 0 m θ
      have hshift : ∀ y ∈ U, f (y, (r, θ)) =
          iteratedDeriv 0 (H.decode (g y) m) θ + c := by
        intro y hy
        simpa only [iteratedDeriv_zero, add_comm] using heq y hy θ
      have hsame := P.positive_jet_eq_of_constant_shift Q c hshift n x hx v
      simp only [Nat.succ_ne_zero, if_false, zero_add]
      calc
        _ = P.D (n + 1) x v :=
          (J.freezeSpatial_apply K.open_domain (r, θ) hp (n + 1) x v).symm
        _ = Q.D (n + 1) x v := hsame
        _ = _ := by
          simpa only [Q, iteratedDeriv_zero] using
            circleDecodedAngularDirections_jet hH K 0 m θ (n + 1) x v

/-- For an affine decoder, the constant survives exactly at parameter
order zero and angular order zero. All positive jets are the genuine
circle jets of the perturbation. -/
theorem jointMixedDiagonal_eq_circleAngularJet_add_const
    (J : SmoothDirections (U ×ˢ (Ioo l h ×ˢ univ)) f)
    (hH : IsCircleModel T γ H) (K : SmoothDirections U g)
    (m : ℕ) (hr : r ∈ Ioo l h) (c : ℝ)
    (heq : ∀ x ∈ U, ∀ θ, f (x, (r, θ)) = c + H.decode (g x) m θ)
    (n b : ℕ) (x w : E) (hx : x ∈ U) (θ : ℝ) :
    jointMixedDiagonal J n 0 b x w (r, θ) =
      (if n = 0 ∧ b = 0 then c else 0) +
        iteratedDeriv b (H.decode (K.D n x (fun _ => w)) m) θ := by
  have hfun : (fun θ => J.D n (x, (r, θ))
      (fun _ : Fin n => (w, (0 : PolarPoint)))) =
      fun θ => (if n = 0 then c else 0) + H.decode (K.D n x (fun _ => w)) m θ := by
    funext φ
    exact J.jointJet_eq_circleDecoded_add_const hH K m hr c heq n x hx (fun _ => w) φ
  simp only [jointMixedDiagonal, mixedDerivative, iteratedDeriv_zero]
  rw [hfun]
  cases b with
  | zero => simp only [iteratedDeriv_zero, eq_self_iff_true, and_true]
  | succ b =>
      rw [iteratedDeriv_const_add (Nat.succ_pos b) (if n = 0 then c else 0)]
      simp only [Nat.succ_ne_zero, and_false, if_false, zero_add]

end ContinuousFlexibility.Analysis
