import Mathmatica.SATSymmetry
import Mathmatica.SATDecimation

/-!
# 猜想桥 III：等变重整化与对称性破缺（Equivariant Renormalization Group）

本模块形式化并证明实空间重整化（Davis-Putnam 变量抽取 `decimateVar`）与
布尔公式对称群（`Equiv.Perm (Fin n)`）之间的精确交互定理：

1. **文字与剥离的置换等变性**：
   - `hasLit_actClause`：`hasLit (actClause π c) (π v) pol = hasLit c v pol`
   - `stripVar_actClause`：`stripVar (π v) (actClause π c) = actClause π (stripVar v c)`
2. **核心定理 1（实空间重整化算子的群等变性）**：
   - `decimateVar_equivariant`：`actCNF π (decimateVar v φ) = decimateVar (π v) (actCNF π φ)`
   （且在子句列表顺序层面严格相等，无需重排。）
   - `decimateList_equivariant`：多变量顺序抽取的群等变性。
3. **核心定理 2（不动点变量消元保持公式对称性）**：
   - `decimateVar_preserves_symmetry`：若 `actCNF π φ = φ` 且 `π v = v`，
     则 `actCNF π (decimateVar v φ) = decimateVar v φ`。
   - `decimateList_preserves_symmetry`：依次消去不动点变量列表仍保持对称性。
4. **核心定理 3（对称轨道与解空间的联合重整化推论）**：
   - `decimateVar_preserves_symmetryGroup` / `decimateVar_solSpace_invariant` /
     `decimateVar_preserves_group_and_solSpace`：
     若 `G` 是 `φ` 的对称群且 `v` 是 `G` 的公共不动点（`∀ π ∈ G, π v = v`），
     则 `G` 依然是 `decimateVar v φ` 的对称群，且 `decimateVar v φ` 的解空间保持 `G`-不变性。
   - `decimateVar_sbp_equisatisfiable`：等变重整化与对称性破缺谓词（SBP）联合后的等可满足性。
-/

namespace Mathmatica.EquivariantRG

open Mathmatica.SAT
open Mathmatica.SATDecimation

/-! ## 第一部分：文字查询与变量剥离的置换等变性 -/

private lemma beq_perm_eq {n : ℕ} (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    (π a == π b) = (a == b) := by
  by_cases h : a = b
  · rw [h, beq_self_eq_true, beq_self_eq_true]
  · have h' : π a ≠ π b := fun heq => h (π.injective heq)
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

/-- 辅助引理：子句拼接与置换作用可交换。 -/
lemma actClause_append {n : ℕ} (π : Equiv.Perm (Fin n)) (p q : Clause n) :
    actClause π (p ++ q) = actClause π p ++ actClause π q := by
  simp only [actClause, List.map_append]

/-- 辅助引理：CNF 拼接与置换作用可交换。 -/
lemma actCNF_append {n : ℕ} (π : Equiv.Perm (Fin n)) (φ₁ φ₂ : CNF n) :
    actCNF π (φ₁ ++ φ₂) = actCNF π φ₁ ++ actCNF π φ₂ := by
  simp only [actCNF, List.map_append]

/-- **引理 1（文字包含检测的置换等变性）**：
对子句 `c` 与变量 `v` 同时施加置换 `π`，文字存在性查询 `hasLit` 保持不变。 -/
lemma hasLit_actClause {n : ℕ} (π : Equiv.Perm (Fin n)) (c : Clause n) (v : Fin n) (pol : Bool) :
    hasLit (actClause π c) (π v) pol = hasLit c v pol := by
  unfold hasLit actClause
  rw [List.any_map]
  congr 1
  funext l
  dsimp [Function.comp, actLiteral]
  rw [beq_perm_eq]

/-- **引理 2（变量剥离的置换等变性）**：
先对子句施加置换 `π` 再剥离 `π v`，严格等于先剥离 `v` 再施加置换 `π`。 -/
lemma stripVar_actClause {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) (c : Clause n) :
    stripVar (π v) (actClause π c) = actClause π (stripVar v c) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    unfold stripVar actClause at ih ⊢
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    have hbne : ((actLiteral π l).var != π v) = (l.var != v) := by
      change (!(π l.var == π v)) = (!(l.var == v))
      rw [beq_perm_eq]
    rw [hbne]
    cases (l.var != v) <;> simp [ih]

/-! ## 第二部分：实空间重整化算子的群等变性 -/

/-- `restClauses` 在置换作用下的严格等变性（保持子句列表顺序）。 -/
lemma restClauses_actCNF {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) (φ : CNF n) :
    actCNF π (restClauses v φ) = restClauses (π v) (actCNF π φ) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    unfold actCNF restClauses at ih ⊢
    rw [List.filter_cons, List.map_cons, List.filter_cons]
    rw [hasLit_actClause, hasLit_actClause]
    cases (!hasLit c v true && !hasLit c v false) <;> simp [ih]

/-- `posClauses` 在置换作用下的严格等变性（保持子句列表顺序）。 -/
lemma posClauses_actCNF {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) (φ : CNF n) :
    actCNF π (posClauses v φ) = posClauses (π v) (actCNF π φ) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    unfold actCNF posClauses at ih ⊢
    rw [List.filter_cons, List.map_cons, List.filter_cons]
    rw [hasLit_actClause, hasLit_actClause]
    cases (hasLit c v true && !hasLit c v false) <;> simp [stripVar_actClause, ih]

/-- `negClauses` 在置换作用下的严格等变性（保持子句列表顺序）。 -/
lemma negClauses_actCNF {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) (φ : CNF n) :
    actCNF π (negClauses v φ) = negClauses (π v) (actCNF π φ) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    unfold actCNF negClauses at ih ⊢
    rw [List.filter_cons, List.map_cons, List.filter_cons]
    rw [hasLit_actClause, hasLit_actClause]
    cases (!hasLit c v true && hasLit c v false) <;> simp [stripVar_actClause, ih]

private lemma actCNF_flatMap_append {n : ℕ} (π : Equiv.Perm (Fin n)) (ps qs : CNF n) :
    actCNF π (ps.flatMap (fun p => qs.map (fun q => p ++ q))) =
      (actCNF π ps).flatMap (fun p => (actCNF π qs).map (fun q => p ++ q)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    unfold actCNF at ih ⊢
    simp only [List.flatMap_cons, List.map_cons, List.map_append]
    rw [ih]
    congr 1
    clear ih
    induction qs with
    | nil => rfl
    | cons q qs ihq =>
      simp only [List.map_cons, actClause_append, ihq]

/-- `resolvents` 在置换作用下的严格等变性（保持两两归结的笛卡尔积列表顺序）。 -/
lemma resolvents_actCNF {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) (φ : CNF n) :
    actCNF π (resolvents v φ) = resolvents (π v) (actCNF π φ) := by
  unfold resolvents
  rw [← posClauses_actCNF, ← negClauses_actCNF]
  exact actCNF_flatMap_append π (posClauses v φ) (negClauses v φ)

/-- **核心定理 1（实空间重整化算子的群等变性）**：
对任意变量置换 `π ∈ S_n` 与变量 `v`，Davis-Putnam 抽取算子 `decimateVar` 满足严格等变性：
`actCNF π (decimateVar v φ) = decimateVar (π v) (actCNF π φ)`。 -/
theorem decimateVar_equivariant {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) (φ : CNF n) :
    actCNF π (decimateVar v φ) = decimateVar (π v) (actCNF π φ) := by
  unfold decimateVar
  rw [actCNF_append, restClauses_actCNF, resolvents_actCNF]

/-- 推论：多变量顺序实空间重整化 `decimateList` 的群等变性。 -/
theorem decimateList_equivariant {n : ℕ} (π : Equiv.Perm (Fin n)) (vs : List (Fin n)) (φ : CNF n) :
    actCNF π (decimateList vs φ) = decimateList (vs.map π) (actCNF π φ) := by
  induction vs generalizing φ with
  | nil => rfl
  | cons v vs ih =>
    simp only [decimateList, List.map_cons]
    rw [ih (decimateVar v φ), decimateVar_equivariant]

/-! ## 第三部分：不动点变量消元保持公式对称性 -/

/-- **核心定理 2（不动点变量消元保持公式对称性）**：
若置换 `π` 是公式 `φ` 的对称变换（`actCNF π φ = φ`），且被消去变量 `v` 是 `π` 的不动点
（`π v = v`），则粗粒化后的有效公式 `decimateVar v φ` 依然以 `π` 为对称变换。 -/
theorem decimateVar_preserves_symmetry {n : ℕ} {π : Equiv.Perm (Fin n)} {v : Fin n} {φ : CNF n}
    (hSym : actCNF π φ = φ) (hFix : π v = v) :
    actCNF π (decimateVar v φ) = decimateVar v φ := by
  rw [decimateVar_equivariant, hFix, hSym]

/-- 推论：依次消去由 `π` 的不动点组成的变量列表 `vs`，仍保持对称性 `π`。 -/
theorem decimateList_preserves_symmetry {n : ℕ} {π : Equiv.Perm (Fin n)} {vs : List (Fin n)}
    {φ : CNF n} (hSym : actCNF π φ = φ) (hFix : ∀ v ∈ vs, π v = v) :
    actCNF π (decimateList vs φ) = decimateList vs φ := by
  induction vs generalizing φ with
  | nil => exact hSym
  | cons v vs ih =>
    simp only [decimateList]
    have hv : π v = v := hFix v List.mem_cons_self
    have hvs : ∀ u ∈ vs, π u = u := fun u hu => hFix u (List.mem_cons_of_mem v hu)
    exact ih (decimateVar_preserves_symmetry hSym hv) hvs

/-! ## 第四部分：对称轨道与解空间的联合重整化推论 -/

/-- 若 `G` 是 `φ` 的对称群且 `v` 是 `G` 的公共不动点，则 `G` 依然是 `decimateVar v φ` 的对称群。 -/
theorem decimateVar_preserves_symmetryGroup {n : ℕ} {φ : CNF n} {v : Fin n}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : ∀ π ∈ G, actCNF π φ = φ)
    (hFix : ∀ π ∈ G, π v = v) :
    ∀ π ∈ G, actCNF π (decimateVar v φ) = decimateVar v φ :=
  fun π hπ => decimateVar_preserves_symmetry (hG π hπ) (hFix π hπ)

/-- 若 `G` 是 `φ` 的对称群且 `v` 是 `G` 的公共不动点，则 `decimateVar v φ` 的解空间保持 `G`-不变性。 -/
theorem decimateVar_solSpace_invariant {n : ℕ} {φ : CNF n} {v : Fin n}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : ∀ π ∈ G, actCNF π φ = φ)
    (hFix : ∀ π ∈ G, π v = v) :
    ∀ π ∈ G, ∀ σ : Assignment n,
      Satisfies (decimateVar v φ) σ → Satisfies (decimateVar v φ) (actAssignment π σ) :=
  fun π hπ _ hSat =>
    satisfies_of_symmetry (decimateVar_preserves_symmetry (hG π hπ) (hFix π hπ)) hSat

/-- **核心定理 3（对称轨道与解空间的联合重整化推论）**：
若 `G` 是公式 `φ` 的对称群（`∀ π ∈ G, actCNF π φ = φ`）且 `v` 是 `G` 的公共不动点
（`∀ π ∈ G, π v = v`），则消去 `v` 后的粗粒化有效公式 `decimateVar v φ` 同时满足：
1. `G` 依然是 `decimateVar v φ` 的对称群；
2. `decimateVar v φ` 的解空间在 `G` 的群作用下保持轨道不变性。 -/
theorem decimateVar_preserves_group_and_solSpace {n : ℕ} {φ : CNF n} {v : Fin n}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : ∀ π ∈ G, actCNF π φ = φ)
    (hFix : ∀ π ∈ G, π v = v) :
    (∀ π ∈ G, actCNF π (decimateVar v φ) = decimateVar v φ) ∧
    (∀ π ∈ G, ∀ σ : Assignment n,
      Satisfies (decimateVar v φ) σ → Satisfies (decimateVar v φ) (actAssignment π σ)) :=
  ⟨decimateVar_preserves_symmetryGroup G hG hFix,
   decimateVar_solSpace_invariant G hG hFix⟩

/-- **联合推论（等变重整化 + 对称性破缺谓词 SBP 的联合等可满足性）**：
在 `G` 为 `φ` 的对称群且 `v` 为 `G` 的公共不动点时，对任意 `G`-轨道代表元谓词 `P`（SBP），
先对 `v` 执行实空间重整化再施加对称性破缺约束 `P`，与原公式 `φ` 严格等可满足。 -/
theorem decimateVar_sbp_equisatisfiable {n : ℕ} {φ : CNF n} {v : Fin n}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : ∀ π ∈ G, actCNF π φ = φ)
    (hFix : ∀ π ∈ G, π v = v)
    (P : Assignment n → Prop)
    (hRep : ∀ σ : Assignment n, ∃ π ∈ G, P (actAssignment π σ)) :
    (∃ σ : Assignment n, Satisfies (decimateVar v φ) σ ∧ P σ) ↔ Satisfiable φ := by
  rw [sbp_equisatisfiable G (decimateVar_preserves_symmetryGroup G hG hFix) P hRep]
  exact decimateVar_equisatisfiable v φ

end Mathmatica.EquivariantRG
