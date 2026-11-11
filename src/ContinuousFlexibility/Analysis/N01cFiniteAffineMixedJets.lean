import ContinuousFlexibility.Analysis.N01cFiniteAffineJets
import ContinuousFlexibility.Analysis.N01cOpticalMixedJets

/-!
# Finite affine identification of mixed state and angular derivatives

Only the finite real parameter spaces are normed. Genuine state towers
on the original topological state space are identified on those affine
restrictions, where ordinary mixed derivative commutation applies.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem finiteAffine_smoothDirections_zero
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f)
    {x : E} (hx : x ∈ U) (v : Fin 0 → E) : J.D 0 x v = f x := by
  have hv : v = (Fin.elim0 : Fin 0 → E) := by
    funext i
    exact i.elim0
  rw [hv]
  exact J.zero x hx

section NormedSlices

variable {X P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A jointly smooth finite-dimensional family has jointly smooth
fixed-direction evaluations of every supplied genuine state jet. -/
theorem contDiffOn_stateJetEvaluation
    {U : Set X} {V : Set P} (hU : IsOpen U) (hV : IsOpen V)
    {f : X × P → ℝ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ V))
    (J : ∀ q : P, SmoothDirections U (fun x => f (x, q)))
    (n : ℕ) (v : Fin n → X) :
    ContDiffOn ℝ ∞ (fun z : X × P => (J z.2).D n z.1 v) (U ×ˢ V) := by
  induction n with
  | zero =>
      apply hf.congr
      intro z hz
      exact finiteAffine_smoothDirections_zero (J z.2) hz.1 v
  | succ n ih =>
      let H : X × P → ℝ := fun z => (J z.2).D n z.1 (Fin.tail v)
      have hH : ContDiffOn ℝ ∞ H (U ×ˢ V) := ih (Fin.tail v)
      have hD : ContDiffOn ℝ ∞ (fun z : X × P =>
          fderiv ℝ H z ((v 0), 0)) (U ×ˢ V) :=
        (hH.fderiv_of_isOpen (hU.prod hV) (by simp)).clm_apply contDiffOn_const
      apply hD.congr
      intro z hz
      have hfull : DifferentiableAt ℝ H z :=
        (hH.contDiffAt ((hU.prod hV).mem_nhds hz)).differentiableAt (by simp)
      have hpair : HasFDerivAt (fun y : X => (y, z.2))
          (ContinuousLinearMap.inl ℝ X P) z.1 :=
        hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2
      have hleft : HasFDerivAt (fun y : X => H (y, z.2))
          ((fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ X P)) z.1 := by
        simpa only [Function.comp_def, Prod.eta] using
          hfull.hasFDerivAt.comp (f := fun y : X => (y, z.2)) z.1 hpair
      have hstate := (J z.2).hasProjectiveJetsOn.hasFDerivAt_eval_finiteDimensional
        hU n (Fin.tail v) hz.1
      have he := congrArg (fun L : X →L[ℝ] ℝ => L (v 0)) (hleft.unique hstate)
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        projectiveJetHeadLinear_apply, Fin.cons_self_tail] using he.symm

end NormedSlices

section AngularSlices

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Scalar differentiation in the last coordinate preserves local joint
smoothness on a product of an open parameter set and the whole line. -/
theorem contDiffOn_uncurry_iteratedDeriv
    {V : Set P} (hV : IsOpen V) {f : P → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ (univ : Set ℝ))) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y : P × ℝ => iteratedDeriv n (f y.1) y.2)
      (V ×ˢ (univ : Set ℝ)) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hf
  | succ n ih =>
      intro y hy
      have haux : ContDiffAt ℝ ∞ (fun z : (P × ℝ) × ℝ =>
          iteratedDeriv n (f z.1.1) z.2) (y, y.2) :=
        (ih.contDiffAt ((hV.prod isOpen_univ).mem_nhds hy)).comp (y, y.2)
          ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
      have hderiv : ContDiffAt ℝ ∞ (fun z : P × ℝ =>
          fderiv ℝ (fun s => iteratedDeriv n (f z.1) s) z.2) y :=
        haux.fderiv contDiffAt_snd (by simp)
      have hvalue := hderiv.clm_apply (contDiffAt_const (c := (1 : ℝ)))
      simpa only [iteratedDeriv_succ, fderiv_apply_one_eq_deriv] using
        hvalue.contDiffWithinAt

/-- Angular differentiation with an additional time coordinate. -/
theorem contDiffOn_timeAngularIterate
    {V : Set P} (hV : IsOpen V) {f : P × (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ (univ : Set (ℝ × ℝ)))) (b : ℕ) :
    ContDiffOn ℝ ∞ (fun y : P × (ℝ × ℝ) =>
      iteratedDeriv b (fun θ => f (y.1, (y.2.1, θ))) y.2.2)
      (V ×ˢ (univ : Set (ℝ × ℝ))) := by
  let g : (P × ℝ) → ℝ → ℝ := fun x θ => f (x.1, (x.2, θ))
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g)
      ((V ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) :=
    hf.comp ((contDiffOn_fst.fst).prodMk
      ((contDiffOn_fst.snd).prodMk contDiffOn_snd))
      (fun x hx => ⟨hx.1.1, mem_univ _⟩)
  have hi := contDiffOn_uncurry_iteratedDeriv (hV.prod isOpen_univ) hg b
  exact hi.comp ((contDiffOn_fst.prodMk (contDiffOn_snd.fst)).prodMk
    (contDiffOn_snd.snd)) (fun x hx => ⟨⟨hx.1, mem_univ _⟩, mem_univ _⟩)

end AngularSlices

section FiniteCoordinates

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

private theorem finiteAffine_stateJet_line_deriv
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f)
    (k : ℕ) {x : E} (hx : x ∈ U) (v : Fin k → E) (w : E) :
    HasDerivAt (fun s : ℝ => J.D k (x + s • w) v)
      (J.D (k + 1) x (Fin.cons w v)) (0 : ℝ) := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    zero_add, zero_smul, add_zero, smul_eq_mul] using J.derivative k x hx v w

/-- The actual finite linear combination of the prescribed state
directions, continuously mapped into the original state topology. -/
def finiteDirectionMap {n : ℕ} (v : Fin n → E) : (Fin n → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i)

@[simp] theorem finiteDirectionMap_apply {n : ℕ} (v : Fin n → E) (x : Fin n → ℝ) :
    finiteDirectionMap v x = ∑ i, x i • v i := by
  simp only [finiteDirectionMap, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]

@[simp] theorem finiteDirectionMap_single {n : ℕ} (v : Fin n → E)
    (i : Fin n) (a : ℝ) :
    finiteDirectionMap v (Pi.single i a) = a • v i := by
  rw [finiteDirectionMap_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Only finite real parameter spaces are normed. Time and angle remain
external variables, jointly smooth with every finite affine restriction. -/
def IsFiniteAffineTimeSmooth (U : Set E) (f : E × (ℝ × ℝ) → ℝ) : Prop :=
  ∀ n : ℕ, ∀ x₀ : E, ∀ L : (Fin n → ℝ) →L[ℝ] E,
    ContDiffOn ℝ ∞ (fun z : (Fin n → ℝ) × (ℝ × ℝ) => f (x₀ + L z.1, z.2))
      (((fun y => x₀ + L y) ⁻¹' U) ×ˢ (univ : Set (ℝ × ℝ)))

/-- All angular derivatives of a finite affine restriction are jointly
smooth on exactly the same open inverse image of the state domain. -/
theorem IsFiniteAffineTimeSmooth.angular
    {U : Set E} {f : E × (ℝ × ℝ) → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f) (b : ℕ) :
    IsFiniteAffineTimeSmooth U (fun z =>
      iteratedDeriv b (fun θ => f (z.1, (z.2.1, θ))) z.2.2) := by
  intro n x₀ L
  exact contDiffOn_timeAngularIterate
    (hU.preimage (continuous_const.add L.continuous)) (hf n x₀ L) b

/-- Jointly smooth evaluation of the genuine state jets on arbitrary
finite affine restrictions. The directions are their actual images under
the same finite-coordinate linear map. -/
theorem contDiffOn_stateJet_finiteAffine
    {U : Set E} {f : E × (ℝ × ℝ) → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ q : ℝ × ℝ, SmoothDirections U (fun x => f (x, q)))
    (d : ℕ) (x₀ : E) (L : (Fin d → ℝ) →L[ℝ] E)
    (k : ℕ) (v : Fin k → (Fin d → ℝ)) :
    ContDiffOn ℝ ∞ (fun z : (Fin d → ℝ) × (ℝ × ℝ) =>
      (J z.2).D k (x₀ + L z.1) (fun i => L (v i)))
      (((fun y => x₀ + L y) ⁻¹' U) ×ˢ (univ : Set (ℝ × ℝ))) := by
  exact contDiffOn_stateJetEvaluation
    (hU.preimage (continuous_const.add L.continuous)) isOpen_univ (hf d x₀ L)
    (fun q => smoothDirections_precompAffine (J q) x₀ L) k v

/-- Fixed-state evaluations are smooth in both external variables. -/
theorem contDiff_stateJet_external
    {U : Set E} {f : E × (ℝ × ℝ) → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ q : ℝ × ℝ, SmoothDirections U (fun x => f (x, q)))
    (k : ℕ) (v : Fin k → E) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => (J q).D k x₀ v) := by
  let L := finiteDirectionMap v
  have h := contDiffOn_stateJet_finiteAffine hU hf J k x₀ L k
    (fun i => Pi.single i (1 : ℝ))
  have hzero : x₀ + L 0 = x₀ := by simp [L]
  have hd : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ =>
      (J q).D k (x₀ + L 0) (fun i => L (Pi.single i (1 : ℝ)))) univ :=
    h.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun q _ => ⟨by simpa only [mem_preimage, hzero] using hx₀, mem_univ q⟩)
  have hv : (fun i => L (Pi.single i (1 : ℝ))) = v := by
    funext i
    simp only [L, finiteDirectionMap_single, one_smul]
  simpa only [hzero, hv, contDiffOn_univ] using hd

/-- Joint smoothness along one additional state line and both external
variables. The pre-existing derivative directions need not lie in that
line: all of them are included in the finite coordinate map. -/
theorem contDiffOn_stateJet_line_external
    {U : Set E} {f : E × (ℝ × ℝ) → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ q : ℝ × ℝ, SmoothDirections U (fun x => f (x, q)))
    (k : ℕ) (v : Fin k → E) (x₀ w : E) :
    ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) =>
      (J z.2).D k (x₀ + z.1 • w) v)
      (((fun t : ℝ => x₀ + t • w) ⁻¹' U) ×ˢ (univ : Set (ℝ × ℝ))) := by
  let L := finiteDirectionMap (Fin.cons w v)
  let e : ℝ →L[ℝ] (Fin (k + 1) → ℝ) :=
    ContinuousLinearMap.single ℝ (fun _ : Fin (k + 1) => ℝ) 0
  have he (t : ℝ) : L (e t) = t • w := by
    simpa only [e, ContinuousLinearMap.single_apply, Fin.cons_zero] using
      finiteDirectionMap_single (Fin.cons w v) 0 t
  have hv : (fun i : Fin k => L (Pi.single i.succ (1 : ℝ))) = v := by
    funext i
    simp only [L, finiteDirectionMap_single, one_smul, Fin.cons_succ]
  have h := contDiffOn_stateJet_finiteAffine hU hf J (k + 1) x₀ L k
    (fun i => Pi.single i.succ (1 : ℝ))
  have hmap : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => (e z.1, z.2))
      (((fun t : ℝ => x₀ + t • w) ⁻¹' U) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (e.contDiff.comp contDiff_fst).contDiffOn.prodMk contDiffOn_snd
  have hd := h.comp hmap
    (fun z hz => ⟨by simpa only [mem_preimage, he] using hz.1, mem_univ _⟩)
  simpa only [Function.comp_def, he, hv] using hd

/-- The actual angular derivative commutes with every actual state jet.
The proof only differentiates smooth real two-dimensional restrictions;
the state space itself is never assigned a norm. -/
theorem deriv_stateJet_angle
    {U : Set E} {f : E × (ℝ × ℝ) → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : ℝ × ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (k : ℕ) : ∀ (b : ℕ) (x : E), x ∈ U → ∀ (t θ : ℝ) (v : Fin k → E),
      deriv (fun η => (J b (t, η)).D k x v) θ =
        (J (b + 1) (t, θ)).D k x v := by
  induction k with
  | zero =>
      intro b x hx t θ v
      have he : (fun η => (J b (t, η)).D 0 x v) =
          iteratedDeriv b (fun η => f (x, (t, η))) := by
        funext η
        exact finiteAffine_smoothDirections_zero (J b (t, η)) hx v
      rw [he, ← iteratedDeriv_succ]
      exact (finiteAffine_smoothDirections_zero (J (b + 1) (t, θ)) hx v).symm
  | succ k ih =>
      intro b x hx t θ v
      let V : Set ℝ := (fun s : ℝ => x + s • v 0) ⁻¹' U
      have hV : IsOpen V := hU.preimage (continuous_const.add
        (continuous_id.smul continuous_const))
      have h0 : (0 : ℝ) ∈ V := by simpa only [V, mem_preimage, zero_smul, add_zero] using hx
      let H : ℝ × ℝ → ℝ := fun p => (J b (t, p.2)).D k (x + p.1 • v 0) (Fin.tail v)
      have hH : ContDiffOn ℝ ∞ H (V ×ˢ (univ : Set ℝ)) :=
        (contDiffOn_stateJet_line_external hU (hf.angular hU b) (J b) k (Fin.tail v)
          x (v 0)).comp
            (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
            (fun p hp => ⟨hp.1, mem_univ _⟩)
      have hhead : (fun η => (J b (t, η)).D (k + 1) x v) =
          fun η => deriv (fun s => H (s, η)) 0 := by
        funext η
        have hd : HasDerivAt (fun s : ℝ => (J b (t, η)).D k (x + s • v 0) (Fin.tail v))
            ((J b (t, η)).D (k + 1) x (Fin.cons (v 0) (Fin.tail v))) (0 : ℝ) :=
          finiteAffine_stateJet_line_deriv (J b (t, η)) k hx (Fin.tail v) (v 0)
        simpa only [H, Fin.cons_self_tail] using hd.deriv.symm
      have hswap := iteratedDeriv_swap_of_contDiffOn (hV.prod isOpen_univ) hH
        1 1 (show (0, θ) ∈ V ×ˢ (univ : Set ℝ) from ⟨h0, mem_univ _⟩)
      have he : (fun s => deriv (fun η => H (s, η)) θ) =ᶠ[𝓝 (0 : ℝ)]
          (fun s => (J (b + 1) (t, θ)).D k (x + s • v 0) (Fin.tail v)) := by
        filter_upwards [hV.mem_nhds h0] with s hs
        exact ih b (x + s • v 0) hs t θ (Fin.tail v)
      have hd : HasDerivAt
          (fun s : ℝ => (J (b + 1) (t, θ)).D k (x + s • v 0) (Fin.tail v))
          ((J (b + 1) (t, θ)).D (k + 1) x (Fin.cons (v 0) (Fin.tail v))) (0 : ℝ) :=
        finiteAffine_stateJet_line_deriv (J (b + 1) (t, θ)) k hx (Fin.tail v) (v 0)
      calc
        _ = deriv (fun η => deriv (fun s => H (s, η)) 0) θ := by rw [hhead]
        _ = deriv (fun s => deriv (fun η => H (s, η)) θ) 0 := by
          simpa only [iteratedDeriv_one] using hswap.symm
        _ = deriv (fun s => (J (b + 1) (t, θ)).D k (x + s • v 0) (Fin.tail v)) 0 :=
          he.deriv_eq
        _ = _ := by simpa only [Fin.cons_self_tail] using hd.deriv

theorem hasDerivAt_stateJet_angle
    {U : Set E} {f : E × (ℝ × ℝ) → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : ℝ × ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (b k : ℕ) {x : E} (hx : x ∈ U) (t θ : ℝ) (v : Fin k → E) :
    HasDerivAt (fun η => (J b (t, η)).D k x v)
      ((J (b + 1) (t, θ)).D k x v) θ := by
  have hs : ContDiff ℝ ∞ (fun η => (J b (t, η)).D k x v) :=
    (contDiff_stateJet_external hU (hf.angular hU b) (J b) k v hx).comp
      (contDiff_const.prodMk contDiff_id)
  have hd := (hs.differentiable (by simp) θ).hasDerivAt
  rw [deriv_stateJet_angle hU hf J k b x hx t θ v] at hd
  exact hd

end FiniteCoordinates

private theorem hasDerivAt_diagonal_of_partials
    {H : ℝ × ℝ → ℝ} (hH : DifferentiableAt ℝ H (0, 0))
    {A B : ℝ} (hA : HasDerivAt (fun s => H (s, 0)) A 0)
    (hB : HasDerivAt (fun s => H (0, s)) B 0) :
    HasDerivAt (fun s => H (s, s)) (A + B) 0 := by
  have hleft : HasDerivAt (fun s : ℝ => H (s, 0))
      (fderiv ℝ H (0, 0) ((1 : ℝ), 0)) (0 : ℝ) := by
    simpa only [Function.comp_def, id_eq] using
      (hH.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, (0 : ℝ))) (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))))
  have hright : HasDerivAt (fun s : ℝ => H (0, s))
      (fderiv ℝ H (0, 0) ((0 : ℝ), 1)) (0 : ℝ) := by
    simpa only [Function.comp_def, id_eq] using
      (hH.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((0 : ℝ), s)) (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))))
  have hdiag : HasDerivAt (fun s : ℝ => H (s, s))
      (fderiv ℝ H (0, 0) ((1 : ℝ), 1)) (0 : ℝ) := by
    simpa only [Function.comp_def, id_eq] using
      (hH.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, s)) (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))))
  have hvalue : fderiv ℝ H (0, 0) ((1 : ℝ), 1) = A + B := by
    have hsum : ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) = ((1 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    calc
      _ = fderiv ℝ H (0, 0) ((1 : ℝ), 0) + fderiv ℝ H (0, 0) ((0 : ℝ), 1) := by
        exact (congrArg (fderiv ℝ H (0, 0)) hsum.symm).trans
          (map_add (fderiv ℝ H (0, 0)) ((1 : ℝ), 0) ((0 : ℝ), 1))
      _ = _ := by rw [hleft.unique hA, hright.unique hB]
  exact hvalue ▸ hdiag

section JointLines

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The genuine joint line differential of every state/angular jet. The
two summands are exactly the state head and angle head of the word lift. -/
theorem hasProjectiveLineDerivAt_stateAngleEvaluation
    {U : Set E} {f : E × (ℝ × ℝ) → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : ℝ × ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (b k : ℕ) {x : E} (hx : x ∈ U) (t θ : ℝ) (v : Fin k → E)
    (w : E × ℝ) :
    HasProjectiveLineDerivAt
      (fun z : E × ℝ => (J b (t, z.2)).D k z.1 v)
      ((J b (t, θ)).D (k + 1) x (Fin.cons w.1 v) +
        w.2 * (J (b + 1) (t, θ)).D k x v) (x, θ) w := by
  let V : Set ℝ := (fun s : ℝ => x + s • w.1) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add
    (continuous_id.smul continuous_const))
  have h0 : (0 : ℝ) ∈ V := by simpa only [V, mem_preimage, zero_smul, add_zero] using hx
  let H : ℝ × ℝ → ℝ := fun p =>
    (J b (t, θ + p.2 * w.2)).D k (x + p.1 • w.1) v
  have hbase : ContDiffAt ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => (J b p.2).D k (x + p.1 • w.1) v) (0, (t, θ)) :=
    (contDiffOn_stateJet_line_external hU (hf.angular hU b) (J b) k v x w.1).contDiffAt
      ((hV.prod isOpen_univ).mem_nhds
        (show (0, (t, θ)) ∈ V ×ˢ (univ : Set (ℝ × ℝ)) from ⟨h0, mem_univ _⟩))
  have hbase' : ContDiffAt ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => (J b p.2).D k (x + p.1 • w.1) v)
      (0, (t, θ + (0 : ℝ) * w.2)) := by
    simpa only [zero_mul, add_zero] using hbase
  have hH : ContDiffAt ℝ ∞ H (0, 0) :=
    hbase'.comp (0, 0)
      (contDiffAt_fst.prodMk (contDiffAt_const.prodMk
        (contDiffAt_const.add (contDiffAt_snd.mul contDiffAt_const))))
  have hstate : HasDerivAt (fun s => H (s, 0))
      ((J b (t, θ)).D (k + 1) x (Fin.cons w.1 v)) 0 := by
    have hd : HasDerivAt (fun s : ℝ => (J b (t, θ)).D k (x + s • w.1) v)
        ((J b (t, θ)).D (k + 1) x (Fin.cons w.1 v)) (0 : ℝ) :=
      finiteAffine_stateJet_line_deriv (J b (t, θ)) k hx v w.1
    dsimp only [H]
    simp only [zero_mul, add_zero]
    exact hd
  have hangle : HasDerivAt (fun s => H (0, s))
      (w.2 * (J (b + 1) (t, θ)).D k x v) 0 := by
    have hinner : HasDerivAt (fun s : ℝ => θ + s * w.2) w.2 0 := by
      simpa only [Pi.add_def, id_eq, zero_add, one_mul] using
        (hasDerivAt_const (0 : ℝ) θ).add ((hasDerivAt_id (0 : ℝ)).mul_const w.2)
    have houter : HasDerivAt (fun η => (J b (t, η)).D k x v)
        ((J (b + 1) (t, θ)).D k x v) (θ + (0 : ℝ) * w.2) := by
      simpa only [zero_mul, add_zero] using hasDerivAt_stateJet_angle hU hf J b k hx t θ v
    have hd := houter.comp 0 hinner
    simpa only [Function.comp_def, H, zero_smul, add_zero, mul_comm] using hd
  have hd : HasDerivAt
      (fun s : ℝ => (J b (t, θ + s * w.2)).D k (x + s • w.1) v)
      ((J b (t, θ)).D (k + 1) x (Fin.cons w.1 v) +
        w.2 * (J (b + 1) (t, θ)).D k x v) (0 : ℝ) :=
    hasDerivAt_diagonal_of_partials (hH.differentiableAt (by simp)) hstate hangle
  change HasProjectiveCurveDerivAt
    (fun s : ℝ => (J b (t, ((x, θ) + s • w).2)).D k ((x, θ) + s • w).1 v)
    ((J b (t, θ)).D (k + 1) x (Fin.cons w.1 v) +
      w.2 * (J (b + 1) (t, θ)).D k x v) (0 : ℝ)
  have hline : (fun s : ℝ =>
      (J b (t, ((x, θ) + s • w).2)).D k ((x, θ) + s • w).1 v) =
      (fun s : ℝ => (J b (t, θ + s * w.2)).D k (x + s • w.1) v) := by
    funext s
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [hline]
  exact hasDerivAt_iff_tendsto_slope_zero.mp hd

end JointLines

end ContinuousFlexibility.Analysis
