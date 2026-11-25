import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

/-!
# 对称性破缺与 $k$-SAT / 计算复杂性（Lean 4 + Mathlib）

本模块形式化：
1. 布尔公式（CNF）与可满足性（SAT）的基本定义。
2. 变量置换群 `Equiv.Perm (Fin n)` 在赋值、文字、子句与 CNF 公式上的作用。
3. **解空间轨道不变性定理**：公式的对称变换将解映射到解。
4. **对称性破缺谓词（SBP）等可满足性定理**（Crawford et al. 1996 思想）：
   若约束 `P` 在每个对称轨道上至少选中一个代表元，则 `φ ∧ P` 可满足当且仅当 `φ` 可满足。
-/

namespace Mathmatica.SAT

/-- `n` 个布尔变量的赋值。 -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- 文字（Literal）：变量编号 + 极性（`true` 表示正文字 `x_i`，`false` 表示负文字 `¬x_i`）。 -/
structure Literal (n : ℕ) where
  var : Fin n
  pol : Bool
  deriving DecidableEq

/-- 子句（Clause）：文字的析取（列表）。 -/
abbrev Clause (n : ℕ) := List (Literal n)

/-- 合取范式（CNF）：子句的合取（列表）。 -/
abbrev CNF (n : ℕ) := List (Clause n)

/-- 赋值 `σ` 满足文字 `l`。 -/
def evalLiteral {n : ℕ} (σ : Assignment n) (l : Literal n) : Bool :=
  σ l.var == l.pol

/-- 赋值 `σ` 满足子句 `c`（至少有一个文字为真）。 -/
def evalClause {n : ℕ} (σ : Assignment n) (c : Clause n) : Bool :=
  c.any (evalLiteral σ)

/-- 赋值 `σ` 满足 CNF 公式 `φ`（所有子句均为真）。 -/
def Satisfies {n : ℕ} (φ : CNF n) (σ : Assignment n) : Prop :=
  ∀ c ∈ φ, evalClause σ c = true

/-- 公式 `φ` 是可满足的（属于 SAT）。 -/
def Satisfiable {n : ℕ} (φ : CNF n) : Prop :=
  ∃ σ : Assignment n, Satisfies φ σ

/-! ## 变量置换群 `S_n` 的作用 -/

/-- 置换 `π` 作用在赋值上：`(π • σ) i = σ (π⁻¹ i)`（标准左群作用）。 -/
def actAssignment {n : ℕ} (π : Equiv.Perm (Fin n)) (σ : Assignment n) : Assignment n :=
  fun i => σ (π⁻¹ i)

/-- 置换 `π` 作用在文字上：将变量 `v` 映射为 `π v`。 -/
def actLiteral {n : ℕ} (π : Equiv.Perm (Fin n)) (l : Literal n) : Literal n :=
  ⟨π l.var, l.pol⟩

/-- 置换 `π` 作用在子句上。 -/
def actClause {n : ℕ} (π : Equiv.Perm (Fin n)) (c : Clause n) : Clause n :=
  c.map (actLiteral π)

/-- 置换 `π` 作用在 CNF 公式上。 -/
def actCNF {n : ℕ} (π : Equiv.Perm (Fin n)) (φ : CNF n) : CNF n :=
  φ.map (actClause π)

/-- 核心引理：同时对赋值和文字施加置换 `π`，真值保持不变（等变性）。 -/
lemma evalLiteral_act {n : ℕ} (π : Equiv.Perm (Fin n)) (σ : Assignment n) (l : Literal n) :
    evalLiteral (actAssignment π σ) (actLiteral π l) = evalLiteral σ l := by
  simp [evalLiteral, actAssignment, actLiteral]

/-- 同时对赋值和子句施加置换 `π`，真值保持不变。 -/
lemma evalClause_act {n : ℕ} (π : Equiv.Perm (Fin n)) (σ : Assignment n) (c : Clause n) :
    evalClause (actAssignment π σ) (actClause π c) = evalClause σ c := by
  unfold evalClause actClause
  rw [List.any_map]
  congr 1
  funext l
  exact evalLiteral_act π σ l

/-- **定理 1（SAT 解空间的对称不变性）**：
如果置换 `π` 保持公式 `φ` 不变（即 `actCNF π φ = φ`），且 `σ` 是 `φ` 的解，
则 `actAssignment π σ` 也是 `φ` 的解。 -/
theorem satisfies_of_symmetry {n : ℕ} {φ : CNF n} {π : Equiv.Perm (Fin n)}
    (hSym : actCNF π φ = φ) {σ : Assignment n} (hSat : Satisfies φ σ) :
    Satisfies φ (actAssignment π σ) := by
  intro c hc
  rw [← hSym] at hc
  unfold actCNF at hc
  rcases List.mem_map.mp hc with ⟨c', hc', rfl⟩
  rw [evalClause_act]
  exact hSat c' hc'

/-- **定理 2（对称性破缺谓词 SBP 的等可满足性定理）**：
设 `G` 是公式 `φ` 的对称群（每个 `π ∈ G` 都满足 `actCNF π φ = φ`），
`P : Assignment n → Prop` 是一个**对称性破缺谓词（Symmetry Breaking Predicate）**，
满足：对任意赋值 `σ`，其 `G`-轨道中至少存在一个代表元 `π • σ` 满足 `P`。
则：**加上对称性破缺约束 `P` 后，原问题依然等可满足**。 -/
theorem sbp_equisatisfiable {n : ℕ} {φ : CNF n}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : ∀ π ∈ G, actCNF π φ = φ)
    (P : Assignment n → Prop)
    (hRep : ∀ σ : Assignment n, ∃ π ∈ G, P (actAssignment π σ)) :
    (∃ σ : Assignment n, Satisfies φ σ ∧ P σ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨σ, hSat, _⟩
    exact ⟨σ, hSat⟩
  · rintro ⟨σ, hSat⟩
    rcases hRep σ with ⟨π, hπ, hP⟩
    exact ⟨actAssignment π σ, satisfies_of_symmetry (hG π hπ) hSat, hP⟩

end Mathmatica.SAT
