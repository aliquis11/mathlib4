import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Completion

noncomputable section

open scoped ComplexConjugate

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem mem_adjoint_domain_iff_exists
    (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (y : F) :
    y ∈ T.adjoint.domain ↔
      ∃ w : E, ∀ x : T.domain,
        inner 𝕜 w (x : E) = inner 𝕜 y (T x) := by
  constructor
  · intro hy
    exact ⟨T.adjoint ⟨y, hy⟩, LinearPMap.adjoint_isFormalAdjoint hT ⟨y, hy⟩⟩
  · exact LinearPMap.mem_adjoint_domain_of_exists y

theorem isSelfAdjoint_of_surjective
    (A : E →ₗ.[𝕜] E)
    (hA_dense : Dense (A.domain : Set E))
    (hA_symm : A.IsFormalAdjoint A)
    (hA_surj : Function.Surjective (fun x : A.domain => A x)) :
    IsSelfAdjoint A := by
    ext x
    constructor
    · intro hx
      change x ∈ A.adjoint.domain at hx
      rw [LinearPMap.mem_adjoint_domain_iff_exists A hA_dense x] at hx
      rcases hx with ⟨f, hpair⟩
      rcases hA_surj f with ⟨x', hx'⟩
      dsimp at hx'
      have hinner (y : A.domain) :
          inner 𝕜 (x' : E) (A y) = inner 𝕜 x (A y) := by
          rw [← hA_symm x' y]
          rw [hx']
          apply hpair y
      have hxx': x = (x' : E) := by
        apply ext_inner_right 𝕜
        intro y
        rcases hA_surj y with ⟨z, hz⟩
        rw [← hz, hinner z]
      simp [hxx']

    · intro hx
      exact (hA_symm.le_adjoint hA_dense).1 hx
    · symm
      apply (hA_symm.le_adjoint hA_dense).2
      simp






end LinearPMap

namespace Friedrichs

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

variable (S : H →ₗ.[𝕜] H)
variable (hsym : S.IsFormalAdjoint S)
variable (hpos : ∀ u : S.domain, u ≠ 0 →
  0 < RCLike.re (inner 𝕜 (u : H) (S u)))

-- Include the proofs in the space's parameters.
def FormSpace
    (S : H →ₗ.[𝕜] H)
    (_hsym : S.IsFormalAdjoint S)
    (_hpos : ∀ u : S.domain, u ≠ 0 →
      0 < RCLike.re (inner 𝕜 (u : H) (S u))) :
    Type _ := S.domain

instance :
    AddCommGroup (FormSpace S hsym hpos) :=
  inferInstanceAs (AddCommGroup S.domain)

instance :
    Module 𝕜 (FormSpace S hsym hpos) :=
  inferInstanceAs (Module 𝕜 S.domain)

@[instance_reducible]
def InnerProductFormSpace :
    InnerProductSpace.Core 𝕜 (FormSpace S hsym hpos) := by
  refine
    { inner := fun (u v : S.domain) =>
        inner 𝕜 (u : H) (S v)
      conj_inner_symm := by
        intro u v
        simp [← hsym u v]
      re_inner_nonneg := by
        intro u
        by_cases hu: u=0
        · rw [hu]
          change 0 ≤ RCLike.re (inner 𝕜 (0 : H) (S 0))
          simp
        · bound [hpos u hu]
      add_left := by
        intro u v w
        apply inner_add_left
      smul_left := by
        intro u v w
        apply inner_smul_left
      definite := by
        intro u huinnerzero
        by_contra hu
        have hposu := hpos u hu
        simp [huinnerzero] at hposu }

instance FormInnerProductSpaceCore :
    InnerProductSpace.Core 𝕜 (FormSpace S hsym hpos) :=
  InnerProductFormSpace S hsym hpos

instance FormNormedAddCommGroup :
    NormedAddCommGroup (FormSpace S hsym hpos) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := 𝕜)
    (cd := InnerProductFormSpace S hsym hpos)

instance FormInnerProductSpace :
    InnerProductSpace 𝕜 (FormSpace S hsym hpos) :=
  InnerProductSpace.ofCore
    (InnerProductFormSpace S hsym hpos).toCore

variable (c : ℝ) (hc : 0 < c)
variable (hbound : ∀ u : S.domain,
  c * ‖(u : H)‖ ^ 2 ≤
    RCLike.re (inner 𝕜 (u : H) (S u)))

instance : CoeOut (FormSpace S hsym hpos) H :=
  ⟨fun u => u.val⟩

theorem exists_formCompletion_inclusion
    [CompleteSpace H]
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ u : S.domain,
      c * ‖(u : H)‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (u : H) (S u))) :
    ∃ J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H,
      Function.Injective J ∧
      ∀ u : FormSpace S hsym hpos,
        J (u : UniformSpace.Completion (FormSpace S hsym hpos)) =
          (u : H) ∧
      ∀ w : UniformSpace.Completion (FormSpace S hsym hpos),
        c * ‖J w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    let j : FormSpace S hsym hpos →ₗ[𝕜] H :={
    toFun u := (u : H)
    map_add':= by
      intro u v
      rfl
    map_smul' := by
      intro a u
      rfl
    }
    have jbound : ∀ u : FormSpace S hsym hpos,
      ‖(u : H)‖  ≤ 1/Real.sqrt c * ‖u‖:= by
      intro u
      rw [← mul_le_mul_iff_right₀ (Real.sqrt_pos.2 hc),← mul_assoc]
      field_simp
      rw [← sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg (u : H)))
      (norm_nonneg u),mul_pow]
      rw [Real.sq_sqrt hc.le]
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜) u]
      exact hbound u
    let jContinuous : FormSpace S hsym hpos →L[𝕜] H :=
      j.mkContinuous (1 / Real.sqrt c) jbound
    let J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H :=
      jContinuous.fromCompletion
    use J
    constructor
    · intro v₁ v₂ hv
      rw [← sub_eq_zero]

      have hInnerOnCompletion : ∀ (u : FormSpace S hsym hpos)
          (v : UniformSpace.Completion (FormSpace S hsym hpos)),
          inner 𝕜
          v (u : UniformSpace.Completion (FormSpace S hsym hpos)) =
          inner 𝕜 (J v) (S (u : S.domain))  := by
        intro u v
        apply UniformSpace.Completion.ext'
            (f := fun w => inner 𝕜
            w (u : UniformSpace.Completion (FormSpace S hsym hpos)))
            (g := fun w => inner 𝕜
            (J w) (S (u : S.domain)))
        · exact Continuous.inner (continuous_id) (continuous_const)
        · exact Continuous.inner (J.continuous) (continuous_const)
        · intro w
          rw[UniformSpace.Completion.inner_coe, ContinuousLinearMap.fromCompletion_apply_coe]
          rfl

      have hOrthogonalToFormSpace: ∀ u : FormSpace S hsym hpos,
      (inner 𝕜 ((J (v₁-v₂)):H) (S u))=0  := by
        intro u
        rw [J.map_sub,hv,sub_self]
        simp

      have hFormSpaceDense : DenseRange
        (fun u : FormSpace S hsym hpos =>
        (u : UniformSpace.Completion (FormSpace S hsym hpos))) :=
        UniformSpace.Completion.denseRange_coe

      apply hFormSpaceDense.eq_zero_of_inner_left 𝕜
      intro u
      rw [hInnerOnCompletion u (v₁-v₂)]
      exact hOrthogonalToFormSpace u
    · intro u
      constructor
      · rw [ContinuousLinearMap.fromCompletion_apply_coe]
        rfl
      · intro w
        apply UniformSpace.Completion.induction_on w
            (p := fun w => c* ‖J w‖^2 ≤ ‖w‖^2)
        · apply isClosed_le
          · exact (continuous_const.mul (J.continuous.norm.pow 2))
          · exact (continuous_norm.pow 2)
        · intro a
          rw [ContinuousLinearMap.fromCompletion_apply_coe, UniformSpace.Completion.norm_coe]
          change c * ‖(a : H)‖^2 ≤ ‖a‖^2
          rw [norm_sq_eq_re_inner (𝕜 := 𝕜) a]
          exact hbound a



theorem exists_unique_form_representative
    [CompleteSpace H]
    (J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H)
    (f : H) :
    ∃! w : UniformSpace.Completion (FormSpace S hsym hpos),
      ∀ v : UniformSpace.Completion (FormSpace S hsym hpos),
        inner 𝕜 w v = inner 𝕜 f (J v) := by
  have hex := (InnerProductSpace.toDual 𝕜
    (UniformSpace.Completion (FormSpace S hsym hpos))).bijective.existsUnique
    ((innerSL 𝕜 f).comp J)

  convert hex
  simp[ContinuousLinearMap.ext_iff]

def RieszRepresentative
    (J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H)
    (f : H) :=
  (InnerProductSpace.toDual 𝕜
    (UniformSpace.Completion (FormSpace S hsym hpos))).symm
    ((innerSL 𝕜 f).comp J)

section FriedrichsTheorems

variable [CompleteSpace H]
variable (hS_dense : Dense (S.domain : Set H))
variable (c : ℝ) (hc : 0 < c)
variable (hbound : ∀ u : S.domain,
  c * ‖(u : H)‖ ^ 2 ≤
    RCLike.re (inner 𝕜 (u : H) (S u)))
variable
  (J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H)
  (hJ_injective : Function.Injective J)
  (hJ_agrees : ∀ u : FormSpace S hsym hpos,
    J (u : UniformSpace.Completion (FormSpace S hsym hpos)) =
      (u : H))
  (hJ_dense : DenseRange J)
  (hJ_bound : ∀ w : UniformSpace.Completion (FormSpace S hsym hpos),
    c * ‖J w‖ ^ 2 ≤ ‖w‖ ^ 2)

include hJ_agrees
theorem inner_formCompletion
    (u : FormSpace S hsym hpos)
    (v : UniformSpace.Completion (FormSpace S hsym hpos)) :
    inner 𝕜 v (u : UniformSpace.Completion (FormSpace S hsym hpos)) =
      inner 𝕜 (J v) (S (u : S.domain)) := by
  apply UniformSpace.Completion.ext'
      (f := fun w => inner 𝕜
        w (u : UniformSpace.Completion (FormSpace S hsym hpos)))
      (g := fun w => inner 𝕜 (J w) (S (u : S.domain)))
  · exact Continuous.inner continuous_id continuous_const
  · exact Continuous.inner J.continuous continuous_const
  · intro w
    rw [UniformSpace.Completion.inner_coe, hJ_agrees w]
    rfl

include hS_dense hc hbound hJ_injective hJ_agrees hJ_dense hJ_bound

-- 1. Construct an extension, including its lower bound.
theorem friedrichs_exists :
    ∃ A : H →ₗ.[𝕜] H,
      S ≤ A ∧
      IsSelfAdjoint A ∧
      (∀ x : A.domain,
        ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
          J w = (x : H)) ∧
      (∀ x : A.domain,
        c * ‖(x : H)‖ ^ 2 ≤
          RCLike.re (inner 𝕜 (x : H) (A x))) := by
  let D : Submodule 𝕜 H :=
    { carrier :=
        {x | ∃ f : H,
        ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = x ∧
        ∀ v : UniformSpace.Completion (FormSpace S hsym hpos),
        inner 𝕜 w v = inner 𝕜 f (J v)
        }
      zero_mem' := by
        use 0
        use 0
        simp
      add_mem' := by
        rintro x₁ x₂ ⟨f₁, w₁, hw₁, hinner₁⟩ ⟨f₂, w₂, hw₂, hinner₂⟩
        use f₁ + f₂
        use w₁ + w₂
        constructor
        · simp [hw₁, hw₂]
        · intro v
          simp [inner_add_left, hinner₁ v, hinner₂ v]
      smul_mem' := by
        rintro a x ⟨f, w, hw, hinner⟩
        use a • f
        use a • w
        constructor
        · simp [hw]
        · intro v
          simp [inner_smul_left, hinner v]
    }
  have output_unique (x f g : H)
    (hf : ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
      J w = x ∧ ∀ v, inner 𝕜 w v = inner 𝕜 f (J v))
    (hg : ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
      J w = x ∧ ∀ v, inner 𝕜 w v = inner 𝕜 g (J v)) :
    f = g := by
    rcases hf with ⟨w₁, hw₁, hp₁⟩
    rcases hg with ⟨w₂, hw₂, hp₂⟩
    have hw : w₁ = w₂ := by
      apply hJ_injective
      rw [hw₁,hw₂]
    apply hJ_dense.eq_of_inner_left 𝕜
    intro v
    rw [← hp₁ v, ← hp₂ v, hw]

  let A : H →ₗ.[𝕜] H :=
    { domain := D
      toFun :=
        { toFun := fun x => Classical.choose x.property
          map_add' := by
            intro x₁ x₂
            apply output_unique ((x₁ + x₂ : D) : H)
            · exact Classical.choose_spec (x₁ + x₂).property
            · rcases Classical.choose_spec x₁.property with ⟨w₁, hw₁, hpair₁⟩
              rcases Classical.choose_spec x₂.property with ⟨w₂, hw₂, hpair₂⟩
              use (w₁+w₂)
              constructor
              · simp [hw₁, hw₂]
              · intro v
                simp [inner_add_left, hpair₁ v, hpair₂ v]
          map_smul' := by
            rintro a x
            rcases Classical.choose_spec x.property with ⟨w, hw, hpair⟩
            apply output_unique ((a • x : D) : H)
            · exact Classical.choose_spec (a • x).property
            · rcases Classical.choose_spec (a • x).property with ⟨aw, haw, hapair⟩
              use (a • w)
              constructor
              · simp [hw]
              · intro v
                simp [inner_smul_left, hpair v]
          }
    }
  use A
  have A_apply_iff (x : A.domain) (f : H) :
    A x = f ↔
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = (x : H) ∧
        ∀ v : UniformSpace.Completion (FormSpace S hsym hpos),
          inner 𝕜 w v = inner 𝕜 f (J v) := by
    constructor
    · intro h
      rw[← h]
      exact Classical.choose_spec x.property
    · intro h
      rcases h with ⟨w, hw, hpair⟩
      apply output_unique (x : H) (A x) f
      · exact Classical.choose_spec x.property
      · use w

  have hSA : S ≤ A := by
    constructor
    · intro x hx
      use S ⟨x,hx⟩
      let x' : FormSpace S hsym hpos := ⟨x, hx⟩
      use (x' : UniformSpace.Completion (FormSpace S hsym hpos))
      constructor
      · apply hJ_agrees x'
      · intro v
        rw [← inner_conj_symm (𝕜 := 𝕜) (↑x') v,
             ← inner_conj_symm (𝕜 := 𝕜) (S ⟨x, hx⟩) (J v)]
        rw [inner_formCompletion S hsym hpos J hJ_agrees x' v]
    · intro x₁ x₂ hx₁₂
      symm
      rw [A_apply_iff x₂ (S x₁)]
      rw [← hx₁₂]
      let x' : FormSpace S hsym hpos := x₁
      use (x' : UniformSpace.Completion (FormSpace S hsym hpos))
      constructor
      · apply hJ_agrees x'
      · intro v
        rw [← inner_conj_symm (𝕜 := 𝕜) (↑x') v,
             ← inner_conj_symm (𝕜 := 𝕜) (S x₁) (J v)]
        rw [inner_formCompletion S hsym hpos J hJ_agrees x' v]

  have hA_dense : Dense (A.domain : Set H) :=
      hS_dense.mono hSA.1

  have hA_surj : ∀ f : H, ∃ z : A.domain, A z = f := by
      intro f
      have h := exists_unique_form_representative S hsym hpos J f
      rcases h with ⟨w, hpair, hw_unique⟩
      have hz : J w ∈ A.domain := by
        use f
        use w
      use ⟨J w, hz⟩
      rw [A_apply_iff]
      use w

  have hA_symm : A.IsFormalAdjoint A := by
    intro x₁ x₂
    rcases Classical.choose_spec x₁.property with ⟨w₁, hw₁, hpair₁⟩
    rcases Classical.choose_spec x₂.property with ⟨w₂, hw₂, hpair₂⟩
    change ∀ v, inner 𝕜 w₁ v = inner 𝕜 (A x₁) (J v) at hpair₁
    change ∀ v, inner 𝕜 w₂ v = inner 𝕜 (A x₂) (J v) at hpair₂
    rw [← hw₂, ← hpair₁ w₂]
    rw [← hw₁,← inner_conj_symm (𝕜 := 𝕜) (J w₁) (A x₂), ← hpair₂ w₁,
        ← inner_conj_symm (𝕜 := 𝕜) w₁ w₂]

  constructor
  · exact hSA
  · constructor
    · exact LinearPMap.isSelfAdjoint_of_surjective A hA_dense hA_symm hA_surj
    · constructor
      · intro x
        rcases Classical.choose_spec x.property with ⟨w, hw, hpair⟩
        use w
      · intro x
        rcases Classical.choose_spec x.property with ⟨w, hw, hpair⟩
        change ∀ v, inner 𝕜 w v = inner 𝕜 (A x) (J v) at hpair
        rw [← hw, inner_re_symm (𝕜 := 𝕜) (J w) (A x)]
        rw [← hpair (w : UniformSpace.Completion (FormSpace S hsym hpos))]
        simp
        exact hJ_bound w




















-- 2. Characterise any such extension by the pairing identity.
theorem friedrichs_pairing_iff
    (A : H →ₗ.[𝕜] H)
    (hA : IsSelfAdjoint A)
    (hSA : S ≤ A)
    (hA_domain : ∀ x : A.domain,
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = (x : H))
    (x f : H) :
    (∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = f) ↔
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = x ∧
        ∀ v : UniformSpace.Completion (FormSpace S hsym hpos),
          inner 𝕜 w v = inner 𝕜 f (J v) := by
  sorry

-- 3. Inlcusion of compeltion of form domain charaterises the extension uniquely.
theorem friedrichs_unique
    (A B : H →ₗ.[𝕜] H)
    (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B)
    (hSA : S ≤ A)
    (hSB : S ≤ B)
    (hA_domain : ∀ x : A.domain,
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = (x : H))
    (hB_domain : ∀ x : B.domain,
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = (x : H)) :
    A = B := by
  sorry

-- 4. Combine existence and uniqueness.
theorem exists_unique_friedrichs_extension :
    ∃! A : H →ₗ.[𝕜] H,
      IsSelfAdjoint A ∧
      S ≤ A ∧
      ∀ x : A.domain,
        ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
          J w = (x : H) := by
  sorry

end FriedrichsTheorems
end Friedrichs
